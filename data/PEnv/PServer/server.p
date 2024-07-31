machine Server
{
  start state Init {
    entry {
      goto Loop;
    }
  }

  state Loop {
    entry {}
    on writeReq do (input: (dest: server, k: key, value: int)) {}
    on readReq do (input: (dest: server, k: key)) {}
  }
}
