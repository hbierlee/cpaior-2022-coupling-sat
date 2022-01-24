predicate array_float_element(var int: i00, array[int] of float: a, var float: z) =
    abort("Not supported");

predicate array_var_float_element(var int: i00, array[int] of var float: a, var float: z) =
    abort("Not supported");

predicate float_abs(var float: x, var float: z) =
  abort("Not supported");

predicate float_eq_reif(var float: x, var float: y, var bool: b) =
  abort("Not supported");

predicate float_le_reif(float: x, var float: y, var bool: b) =
  abort("Not supported");

predicate float_le_reif(var float: x, float: y, var bool: b) =
  abort("Not supported");

predicate float_le_reif(var float: x, var float: y, var bool: b) =
  abort("Not supported");

predicate float_lin_eq_reif(array[int] of float: c, array[int] of var float: x, float: d, var bool: b) =
  abort("Not supported");

predicate float_lin_le_reif(array[int] of float: c, array[int] of var float: x, float: d, var bool: b) =
  abort("Not supported");

predicate float_lin_lt(array[int] of float: c, array[int] of var float: x, float: d) =
  abort("Not supported");

predicate float_lin_lt_reif(array[int] of float: c, array[int] of var float: x, float: d, var bool: b) =
  abort("Not supported");

predicate float_lin_ne_reif(array[int] of float: c, array[int] of var float: x, float: d, var bool: b) =
  abort("Not supported");

predicate float_lt(var float: x, var float: y) =
  abort("Not supported");

predicate float_lt_reif(var float: x, var float: y, var bool: b) =
  abort("Not supported");

predicate float_max(var float: x, var float: y, var float: z) =
  abort("Not supported");

predicate float_min(var float: x, var float: y, var float: z) =
  abort("Not supported");

predicate float_ne(var float: x, float: y) =
  abort("Not supported");

predicate float_ne(var float: x, var float: y) =
  abort("Not supported");

predicate float_ne_reif(var float: x, var float: y, var bool: b) =
  float_eq_reif(x, y, not (b));

predicate float_times(var float: a, var float: b, var float: c) =
    abort("Not supported");

