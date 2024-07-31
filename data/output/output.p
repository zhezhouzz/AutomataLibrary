type st = int;
type action = string;
type server = int;
type key = int;
event write: (dest: server, k: key, value: int);
event read: (dest: server, k: key);
machine Client {
  var action_domain: set[string];
  var final_states: set[int];
  var transitions: map[int, map[string, map[int, int]]];
  var world: map[int, map[int, int]];
  var server_machines: seq[machine];
  var server_Domain: set[int];
  var key_Domain: set[int];
  var fuel: int;
  start state Init {
    entry (input: (server_machines: seq[machine], key_Domain: set[int])) {
      qtype_init(input);
      world_init();
      action_domain_init();
      final_states_init();
      transition_init_function();
      goto Loop;
    }

  }
   state Loop {
    entry  {
      if (check_final()) {
        raise halt;
      };
      do_action();
      goto Loop;
    }

  }
  fun action_domain_init () {
    action_domain += ("write");
    action_domain += ("read");
    return ;
  }
  fun get_available_actions (): set[string] {
    var res: set[string];
    var serv: int;
    var y: int;
    res = action_domain;
    foreach (serv in keys(world)) {
      foreach (y in keys(world[serv])) {
        res = intersection(res, keys(transitions[world[serv][y]]));
      };
    };
    return res;
  }
  fun random_event_write (): (dest: int, k: int, value: int) {
    return (dest = choose(server_Domain), k = choose(key_Domain), value = choose(10000));
  }
  fun random_event_read (): (dest: int, k: int) {
    return (dest = choose(server_Domain), k = choose(key_Domain));
  }
  fun validate_write (serv: int,y: int,m: map[int, int],input: (dest: server, k: key, value: int)): (bool, int) {
    var next_state: int;
    var if_valid: bool;
    if_valid = false;
    if (prop_write_0(serv, y, input)) {
      next_state = m[0];
      if_valid = true;
    };
    if (prop_write_1(serv, y, input)) {
      next_state = m[1];
      if_valid = true;
    };
    if (prop_write_2(serv, y, input)) {
      next_state = m[2];
      if_valid = true;
    };
    return (if_valid, next_state);
  }
  fun validate_read (serv: int,y: int,m: map[int, int],input: (dest: server, k: key)): (bool, int) {
    var next_state: int;
    var if_valid: bool;
    if_valid = false;
    if (prop_read_0(serv, y, input)) {
      next_state = m[0];
      if_valid = true;
    };
    return (if_valid, next_state);
  }
  fun next_world_write (input: (dest: server, k: key, value: int)): bool {
    var tmp_world: map[int, map[int, int]];
    var if_valid: bool;
    var serv: int;
    var y: int;
    var res: (bool, int);
    if_valid = true;
    tmp_world = world;
    foreach (serv in keys(world)) {
      foreach (y in keys(world[serv])) {
        res = validate_write(serv, y, transitions[world[serv][y]]["write"], input);
        if ((res).0) {
          world[serv][y] = (res).1;
        } else {
          if_valid = false;
        };
      };
    };
    if (!(if_valid)) {
      world = tmp_world;
    } else {
      send server_machines[(input).dest], write, (dest = (input).dest, k = (input).k, value = (input).value);
    };
    return if_valid;
  }
  fun next_world_read (input: (dest: server, k: key)): bool {
    var tmp_world: map[int, map[int, int]];
    var if_valid: bool;
    var serv: int;
    var y: int;
    var res: (bool, int);
    if_valid = true;
    tmp_world = world;
    foreach (serv in keys(world)) {
      foreach (y in keys(world[serv])) {
        res = validate_read(serv, y, transitions[world[serv][y]]["read"], input);
        if ((res).0) {
          world[serv][y] = (res).1;
        } else {
          if_valid = false;
        };
      };
    };
    if (!(if_valid)) {
      world = tmp_world;
    } else {
      send server_machines[(input).dest], read, (dest = (input).dest, k = (input).k);
    };
    return if_valid;
  }
  fun do_action (): bool {
    var action: string;
    var event_write: (dest: server, k: key, value: int);
    var event_read: (dest: server, k: key);
    action = choose(get_available_actions());
    if (("write" == action)) {
      event_write = random_event_write();
      if (next_world_write(event_write)) {
        return true;
      };
    };
    if (("read" == action)) {
      event_read = random_event_read();
      if (next_world_read(event_read)) {
        return true;
      };
    };
    return false;
  }
  fun check_final (): bool {
    var res: bool;
    var serv: int;
    var y: int;
    res = true;
    foreach (serv in keys(world)) {
      foreach (y in keys(world[serv])) {
        if (!((world[serv][y] in final_states))) {
          res = false;
        };
      };
    };
    return res;
  }
  fun final_states_init () {
    final_states += (4);
    return ;
  }
  fun transition_init_function () {
    transitions = default(map[int, map[string, map[int, int]]]);
    transitions[4] = default(map[string, map[int, int]]);
    transitions[4]["write"] = default(map[int, int]);
    transitions[4]["write"][0] = 4;
    transitions[3] = default(map[string, map[int, int]]);
    transitions[3]["write"] = default(map[int, int]);
    transitions[3]["write"][1] = 4;
    transitions[3]["read"] = default(map[int, int]);
    transitions[3]["read"][0] = 4;
    transitions[2] = default(map[string, map[int, int]]);
    transitions[2]["write"] = default(map[int, int]);
    transitions[2]["write"][1] = 3;
    transitions[2]["read"] = default(map[int, int]);
    transitions[2]["read"][0] = 3;
    transitions[1] = default(map[string, map[int, int]]);
    transitions[1]["write"] = default(map[int, int]);
    transitions[1]["write"][1] = 2;
    transitions[1]["read"] = default(map[int, int]);
    transitions[1]["read"][0] = 2;
    transitions[0] = default(map[string, map[int, int]]);
    transitions[0]["write"] = default(map[int, int]);
    transitions[0]["write"][2] = 1;
  }
  fun prop_write_2 (serv: int,y: int,input: (dest: server, k: key, value: int)): bool {
    var dest: server;
    var k: key;
    var value: int;
    dest = (input).dest;
    k = (input).k;
    value = (input).value;
    return ((((k == y) && !((k != y))) && (dest == serv)) && (((k == y) && (k != y)) && (dest == serv)));
  }
  fun prop_write_1 (serv: int,y: int,input: (dest: server, k: key, value: int)): bool {
    var dest: server;
    var k: key;
    var value: int;
    dest = (input).dest;
    k = (input).k;
    value = (input).value;
    return (((((((((!((k == y)) && !((k != y))) && !((dest == serv))) && (((k == y) && !((k != y))) && !((dest == serv)))) && ((!((k == y)) && !((k != y))) && (dest == serv))) && (((k == y) && !((k != y))) && (dest == serv))) && ((!((k == y)) && (k != y)) && !((dest == serv)))) && (((k == y) && (k != y)) && !((dest == serv)))) && ((!((k == y)) && (k != y)) && (dest == serv))) && (((k == y) && (k != y)) && (dest == serv)));
  }
  fun prop_write_0 (serv: int,y: int,input: (dest: server, k: key, value: int)): bool {
    var dest: server;
    var k: key;
    var value: int;
    dest = (input).dest;
    k = (input).k;
    value = (input).value;
    return (((!((k == y)) && (k != y)) && (dest == serv)) && (((k == y) && (k != y)) && (dest == serv)));
  }
  fun prop_read_0 (serv: int,y: int,input: (dest: server, k: key)): bool {
    var dest: server;
    var k: key;
    dest = (input).dest;
    k = (input).k;
    return (!((dest == serv)) && (dest == serv));
  }
  fun world_init () {
    var elem_0: int;
    var elem_1: int;
    foreach (elem_0 in server_Domain) {
      foreach (elem_1 in key_Domain) {
        world[elem_0][elem_1] = 0;
      };
    };
  }
  fun qtype_init (input: (server_machines: seq[machine], key_Domain: set[int])) {
    server_machines = (input).server_machines;
    server_Domain = mk_index_set((input).server_machines);
    key_Domain = (input).key_Domain;
    return ;
  }
  fun randomEvent2 (actions: set[action]): bool {
    return ((1 + 3) > 4);
  }
}

