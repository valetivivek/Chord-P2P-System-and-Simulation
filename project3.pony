use "collections"
use "random"
use "time"
use "math"

use @printf[I32](fmt: Pointer[U8] tag, ...)

actor Main
  new create(env: Env) =>
    try
      let args = env.args
      let num_peers = args(1)?.u64()?
      let num_requests = args(2)?.u64()?
      P2PNetwork(num_peers, num_requests, env)
    else
      env.out.print("Usage: chord_sim <num_peers> <num_requests>")
    end

actor P2PNetwork
  let bit_size: U64 = 20
  let id_space: U64
  let nodes: Array[Node] = Array[Node]
  var node_ids: Array[U64] = Array[U64]
  var node_map: Map[U64, Node tag] val
  let stats_tracker: LookupStats
  let env: Env
  var stabilizer_timer: Timer tag

  new create(num_peers: U64, num_requests: U64, env': Env) =>
    id_space = U64(1) << bit_size
    node_map = Map[U64, Node tag].create()
    env = env'
    stats_tracker = LookupStats(num_peers, num_requests, env)
    stabilizer_timer = Timer(
      object iso is TimerNotify
        fun ref apply(timer: Timer, count: U64): Bool =>
          for node in nodes.values() do
            node.run_stabilize()
          end
          true
      end,
      5_000_000_000, // 5 seconds
      5_000_000_000  // Every 5 seconds
    )
    init_network(num_peers, num_requests)

  be init_network(num_peers: U64, num_requests: U64) =>
    create_nodes(num_peers)
    assign_ids(num_peers)
    node_map = map_nodes()
    setup_ring()
    initiate_requests(num_requests)

  fun ref create_nodes(count: U64) =>
    var i: U64 = 0
    while i < count do
      nodes.push(Node(i, id_space))
      i = i + 1
    end

  fun ref assign_ids(count: U64) =>
    let rand_gen = Rand(Time.nanos())
    while node_ids.size() < count.usize() do
      let id = rand_gen.int(id_space).u64()
      if not node_ids.contains(id) then
        node_ids.push(id)
      end
    end
    sort_ids()

  fun ref sort_ids() =>
    var i: USize = 0
    while i < node_ids.size() do
      var j: USize = 0
      while j < (node_ids.size() - 1 - i) do
        try
          if node_ids(j)? > node_ids(j+1)? then
            node_ids(j)? = node_ids(j)? xor node_ids(j+1)?
            node_ids(j+1)? = node_ids(j)? xor node_ids(j+1)?
            node_ids(j)? = node_ids(j)? xor node_ids(j+1)?
          end
        end
        j = j + 1
      end
      i = i + 1
    end

  fun ref map_nodes(): Map[U64, Node tag] val =>
    let temp_map: Map[U64, Node tag] trn = recover trn Map[U64, Node tag] end
    var i: USize = 0
    while i < nodes.size() do
      try
        temp_map(node_ids(i)?) = nodes(i)?
      end
      i = i + 1
    end
    consume temp_map

  fun ref setup_ring() =>
    var i: USize = 0
    while i < nodes.size() do
      try
        let id = node_ids(i)?
        let node = nodes(i)?
        let routing_table = node.build_finger_table(id)
        let primary_successor = routing_table(1)?
        node.initialize(routing_table, -1, primary_successor, node_map)
      end
      i = i + 1
    end

  fun ref initiate_requests(request_count: U64) =>
    for id in node_ids.values() do
      try
        let node = node_map(id)?
        node.execute_requests(request_count, id, id_space, node_map, stats_tracker)
      end
    end

actor Node
  var finger_table: Map[U64, U64] val = Map[U64, U64].create()
  var prev_node: U64 = -1
  var next_node: U64 = -1
  var network_map: Map[U64, Node tag] val = Map[U64, Node tag].create()
  var lookup_cache: Map[U64, U64] = Map[U64, U64].create()
  let id_space: U64

  new create(id: U64, id_space': U64) =>
    id_space = id_space'

  be initialize(routing_table: Map[U64, U64] val, prev: U64, next: U64, map: Map[U64, Node tag] val) =>
    finger_table = routing_table
    prev_node = prev
    next_node = next
    network_map = map

  be join_network(existing_node: Node tag) =>
    existing_node.find_next(_address, this)

  be run_stabilize() =>
    _next_node()?.send_notify(this)

  be send_notify(candidate_pred: Node tag) =>
    if (prev_node == -1) or (_distance(candidate_pred.id, _address) < _distance(prev_node, _address)) then
      prev_node = candidate_pred.id
    end

  be exit_network() =>
    _next_node()?.update_predecessor(prev_node)
    _prev_node()?.update_successor(next_node)

  be execute_requests(request_count: U64, self_id: U64, network_size: U64, network_map: Map[U64, Node tag] val, stats: LookupStats tag) =>
    let rand_gen = Rand
    var i: U64 = 0
    while i < request_count do
      let target = rand_gen.int(network_size).u64()
      if target == self_id then
        stats.track_lookup(0, next_node, target, true)
      else
        process_lookup(target, 0, self_id, stats)
      end
      i = i + 1
    end

  be process_lookup(target: U64, origin: U64, hop_count: U64, stats: LookupStats tag) =>
    if lookup_cache.contains(target) then
      stats.track_lookup(hop_count + 1, _address, target, true)
      return
    end
    
    if target == _address then
      stats.track_lookup(hop_count, origin, target, false)
    else
      let next_hop = _select_next_hop(target)
      lookup_cache(target) = next_hop
      network_map(next_hop)?.process_lookup(target, origin, hop_count + 1, stats)
    end

  fun ref build_finger_table(id: U64): Map[U64, U64] val =>
    recover val
      let table = Map[U64, U64]
      for i in Range(1, bit_size.usize() + 1) do
        let position = U64(1) << (i - 1)
        let lookup_target = (id + position) % id_space
        let successor = locate_successor(lookup_target)
        table(position) = successor
      end
      table
    end

  fun ref locate_successor(target: U64): U64 =>
    for id in node_ids.values() do
      if target <= id then
        return id
      end
    end
    try
      node_ids(0)?
    else
      0
    end

actor LookupStats
  var cache_uses: U64 = 0
  var total_hops: U64 = 0
  var lookups_completed: U64 = 0
  let node_count: U64
  let requests_per_node: U64
  let env: Env

  new create(nodes: U64, requests: U64, env': Env) =>
    node_count = nodes
    requests_per_node = requests
    env = env'

  be track_lookup(hops: U64, node: U64, target: U64, cache_used: Bool = false) =>
    lookups_completed = lookups_completed + 1
    total_hops = total_hops + hops
    if cache_used then cache_uses = cache_uses + 1 end

    let total_lookups = node_count * requests_per_node
    if lookups_completed == total_lookups then
      let avg_hops = total_hops.f64() / lookups_completed.f64()
      let cache_use_rate = (cache_uses.f64() / lookups_completed.f64()) * 100.0
      @printf[I32]("Average Hops: %f\nCache Usage Rate: %f%%\n".cstring(), avg_hops, cache_use_rate)
    end
