annotation no_search;
annotation seq_search(array[int] of ann: s) = no_search;
annotation int_search(array[$X] of var int: x, ann: select, ann: choice, ann: explore) = no_search;
annotation bool_search(array[$X] of var bool: x, ann: select, ann: choice, ann: explore) = no_search;
annotation float_search(array[$X] of var float: x, float: prec, ann: select, ann: choice, ann: explore) = no_search;
annotation set_search(array[$X] of var set of int: x, ann: select, ann: choice, ann: explore) = no_search;

