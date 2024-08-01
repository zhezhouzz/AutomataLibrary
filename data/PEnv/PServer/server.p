machine Server
{
  var store: map[int, int];
  start state ServerInit {
    entry {
      goto ServerLoop;
    }
  }

  state ServerLoop {
    entry {
      store[0] = 0;
      store[1] = 0;
      store[2] = 0;
    }
    on writeReq do (input: (source: machine, dest: server, k: key, value: int)) {
      store[input.k] = input.value;
      send input.source, writeResp, (dest = input.dest, k = input.k, value = input.value);
      goto ServerLoop;
    }
    on readReq do (input: (source: machine, dest: server, k: key)) {
      send input.source, readResp, (dest = input.dest, k = input.k, value = store[input.k]);
      goto ServerLoop;
    }
  }
}
