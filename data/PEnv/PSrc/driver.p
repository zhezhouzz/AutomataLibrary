machine Och {
      start state Init {
            entry {
                  // since client
                  var server_machines: seq[machine];
                  var key_domain: set[int];
                  server_machines += (0, new Server());
                  key_domain += (0);
                  key_domain += (1);
                  key_domain += (2);
                  new Client((server_machines = server_machines, key_domain = key_domain)); 
            }
      }
}

module Client = { Client };
module Server = { Server };
test tcSingleClient [main=Och]: (union Client, Server, { Och });