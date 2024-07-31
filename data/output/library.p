fun intersection (s1: set[string], s2: seq[string]): set[string] {
  var res: set[string];
  var elem: string;
  res = s1;
  foreach (elem in s1) {
    if (!(elem in s2)) {
      res -= (elem);
    }
  }
  return res;
}