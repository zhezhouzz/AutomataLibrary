
// Test driver that checks the system with a single Client.
machine TestWithSingleClient
{
  start state Init {
    entry {
      // since client
      SetupClientServerSystem(1);
    }
  }
}

// Test driver that checks the system with multiple Clients.
machine TestWithMultipleClients
{
  start state Init {
    entry {
      // multiple clients between (2, 4)
      SetupClientServerSystem(choose(3) + 2);
    }
  }
}

// creates a random map from accountId's to account balance of size `numAccounts`
fun CreateRandomInitialAccounts(numAccounts: int) : map[int, int]
{
  var i: int;
  var bankBalance: map[int, int];
  while(i < numAccounts) {
    bankBalance[i] = choose(10) + 10; // min 10 in the account
    i = i + 1;
  }
  return bankBalance;
}

// setup the client server system with one bank server and `numClients` clients.
fun SetupClientServerSystem(numClients: int)
{
  var i: int;
  var server: BankServer;
  var account_domain: set[int];
  var initAccBalance: map[int, int];
  var server_machines: seq[machine];
  var amount_domain: set[int];
  var id_domain: set[int];

  // randomly initialize the account balance for all clients
  initAccBalance = CreateRandomInitialAccounts(numClients);
  // create bank server with the init account balance
  server = new BankServer(initAccBalance);

  // before client starts sending any messages make sure we
  // initialize the monitors or specifications
  announce eSpec_BankBalanceIsAlwaysCorrect_Init, initAccBalance;

  account_domain = seq_int_to_set(keys(initAccBalance));
  amount_domain = set_int_from_range(0, 6);
  id_domain = set_int_from_range(0, 6);
  server_machines += (0, server);
  print format("server_machines: {0}", server_machines);
  print format("account_domain: {0}", account_domain);
  print format("amount_domain: {0}", amount_domain);
  print format("id_domain: {0}", id_domain);

  // create the clients
  while(i < sizeof(account_domain)) {
    new Client((server_machines = server_machines, account_domain = account_domain, amount_domain = amount_domain, id_domain = id_domain));
    i = i + 1;
  }
}