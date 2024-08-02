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

fun mk_index_set (s: seq[any]): set[int] {
  var index: int;
  var res: set[int];
  var elem: any;
  index = 0;
  foreach (elem in s) {
    res += (index);
    index = index + 1;
  }
  return res;
}

fun seq_int_to_set (s: seq[int]): set[int] {
  var elem: int;
  var res: set[int];
  foreach (elem in s) {
    res += (elem);
  }
  return res;
}

fun set_int_from_range (min: int, max: int): set[int] {
  var elem: int;
  var res: set[int];
  elem = min;
  while (elem < max) {
    res += (elem);
    elem = elem + 1;
  }
  return res;
}