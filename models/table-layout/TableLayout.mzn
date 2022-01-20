% A model for minimal height table layout (in lines)
% given a fixed pixel width
% with some minimum height reasoning!

array[int,int,int] of int: f_height;
array[int,int,int] of int: f_width;

opt bool: f_randomize;
bool: randomize = f_randomize default false;

array[int] of int: random_configs_idx = if randomize then [ uniform(1,rows*cols) | row in ROWS, col in COLS ] endif;

array[ROWS,COLS,CONFIGS] of int: height =
  if length(f_height) == 0 then
    gen_configs(ROWS,COLS,CONFIGS,config_size,HEIGHT)
  elseif randomize then
    array3d(ROWS,COLS,CONFIGS, [ c | i in 1..rows*cols, c in f_height[1,random_configs_idx[i],CONFIGS] ])
  else
    f_height
  endif;

array[ROWS,COLS,CONFIGS] of int: width =
  if length(f_width) == 0 then
    gen_configs(ROWS,COLS,CONFIGS,config_size,WIDTH)
  elseif randomize then
    array3d(ROWS,COLS,CONFIGS, [ c | i in 1..rows*cols, c in f_width[1,random_configs_idx[i],CONFIGS] ])
  else
    f_width
  endif;

opt int: f_pixelwidth;

int: median_cell_width = median(w in array1d(width) where w>=0)(w)*cols;
int: pixelwidth = f_pixelwidth default median_cell_width;

function int: median(array[int] of int: xs) = median(xs,<>);
function int: median(array[int] of int: xs, opt float: p) =
  let {
    int: median = sort(xs)[round((length(xs)+1) * (p default 0.5))];
  } in median;

opt bool: f_find_pareto;
bool: find_pareto = f_find_pareto default false;


opt int: f_max_cell_size;
int: max_cell_size = f_max_cell_size default 800;



array[int,int] of int: config_size =
  if length(f_width) == 0 then
    array2d(ROWS,COLS, [ uniform(1,maxconfig) | r in ROWS, c in COLS ])
  else
    array2d(F_ROWS, F_COLS, [ count(w in f_width[r,c,..])(w>=0) | r in F_ROWS, c in F_COLS ])
  endif;

function array[int,int,int] of int: gen_configs(set of int: ROWS, set of int: COLS, set of int: CONFIGS, array[int,int] of int: config_size, Dimension: d) =
array3d(ROWS,COLS,CONFIGS, [
 conf
   |
     r in ROWS,
     c in COLS,
     conf in gen_config(config_size[r,c], card(CONFIGS), d) ]);

function array[int] of int: gen_config(int: k, int: n, Dimension: d) =
  let {
    array[int] of int: config = sort([ uniform(1, max_cell_size) | conf in 1..k ]);
  } in (if d == WIDTH then reverse(config) else config endif) ++ [ -1 | i in 1..n-k ];

int: maxconfig;  % maximum configurations per cell

int: rows; % number of rows
int: cols; % number of cols
set of int: ROWS = 1..rows;
set of int: COLS = 1..cols;
set of int: CONFIGS = 1..maxconfig;

set of int: F_ROWS = index_set_1of3(f_width);
set of int: F_COLS = index_set_2of3(f_width);

int: mincellwidth = min([ width[r,c,l] | r in ROWS, c in COLS, l in CONFIGS where width[r,c,l] >= 0 ]);
int: maxcellwidth = max([ width[r,c,l] | r in ROWS, c in COLS, l in CONFIGS ]);										
int: mincellheight = min([ height[r,c,l] | r in ROWS, c in COLS, l in CONFIGS where height[r,c,l] >= 0 ]);
int: maxcellheight = max([ height[r,c,l] | r in ROWS, c in COLS, l in CONFIGS ]);										

int: maxheight = rows * maxcellheight; % maximum height in pixels
										

enum MZN_SAT_TEST = {
  order_binary_binary, % compact ; only coupling; can't use msu3
  order_binary_order, % only coupling, but order objective ; can use msu3
  order_orderBinary_order, % same but with channelling ; objective still order
  order_orderBinaryCrit,
  order_orderBinaryCritIneqs
};
opt MZN_SAT_TEST: f_mzn_sat_test;
MZN_SAT_TEST: mzn_sat_test = f_mzn_sat_test default order_binary_binary;

array[int] of ann: SAT_encodings =  % cell, col (lin), row (obj)
  if mzn_sat_test == order_binary_binary then
    [order_encoded, binary_encoded, binary_encoded]
  elseif mzn_sat_test == order_binary_order then % couple
    [order_encoded, binary_encoded, order_encoded]
  elseif mzn_sat_test == order_orderBinary_order then % channel
    [order_encoded, order_encoded, order_encoded]
  else 
    let { constraint abort("XXX"); } in []
  endif;

ann: SAT_cell_encoding = SAT_encodings[1];
ann: SAT_col_encoding = SAT_encodings[2];
ann: SAT_row_encoding = SAT_encodings[3];

array[int,int] of var CONFIGS: config::output = array2d(ROWS,COLS,[
  let { var CONFIGS: conf::SAT_cell_encoding; } in conf | r in ROWS, c in COLS
]);

enum Dimension = {WIDTH,HEIGHT};

array[int,int,int] of var int: cells = array3d(ROWS,COLS,Dimension, [
  let {
    % TODO lhs domain could be tighter than rhs, which should be incorporated into element's c argument
    array[int] of int: dim = if d == WIDTH then width[r,c,..] else height[r,c,..] endif;

    array[int] of int: dim_r_c_d = [ size | size in dim where size != -1 ];
  } in dim_r_c_d[config[r,c]]::SAT_cell_encoding | r in ROWS, c in COLS, d in Dimension ]);

array[int] of var int: colwidth_crit = if mzn_sat_test in {order_orderBinaryCrit,order_orderBinaryCritIneqs} then [
  let {
    var { d | cell in cells[..,c,WIDTH], d in dom(cell) }: col::SAT_cell_encoding;
  } in col | c in COLS
] endif;

array[int] of var int: rowheight_crit = if mzn_sat_test in {order_orderBinaryCrit,order_orderBinaryCritIneqs} then [
  let {
    var { d | cell in cells[r,..,HEIGHT], d in dom(cell) }: row::SAT_cell_encoding;
  } in row | r in ROWS
] endif;

array[COLS] of var int: colwidth = [
  let {
    var max(cell in cells[..,c,WIDTH])(lb(cell))..maxcellwidth: col::SAT_col_encoding;
  } in col | c in COLS ];

array[ROWS] of var int: rowheight = [
  let {
    var max(cell in cells[r,..,HEIGHT])(lb(cell))..maxcellheight: row::SAT_row_encoding;
  } in row | r in ROWS ];

constraint forall(r in ROWS, c in COLS)(
  if mzn_sat_test in {order_orderBinaryCrit, order_orderBinaryCritIneqs} then
    colwidth_crit[c] >= cells[r,c,WIDTH] /\ rowheight_crit[r] >= cells[r,c,HEIGHT]
  else
    colwidth[c] >= cells[r,c,WIDTH] /\ rowheight[r] >= cells[r,c,HEIGHT]
  endif
);

opt float: f_pixelwidth_factor;
float: pixelwidth_factor = f_pixelwidth_factor default 1.0;

constraint if not find_pareto then sum(colwidth)::binary_encoded <= round(pixelwidth_factor*pixelwidth) endif;


solve :: int_search([config[r,c] | r in ROWS, c in COLS], first_fail, indomain_min, complete)
	  minimize
              sum(rowheight)
            + if find_pareto then sum(colwidth) else 1 endif
          ;

opt int: f_random_seed;
int: random_seed = f_random_seed default -1;

output
    ["f_random_seed = \(random_seed) ;\n"]++
    ["f_pixelwidth = \(if find_pareto then sum(colwidth) else pixelwidth endif) ;\n"]++
    ["config = \(config) ;\n"]++
    ["obj = \(sum(r in rowheight)(fix(r))) ;\n"]++
    ["maxconfig = \(maxconfig) ;\n"]++
    ["rows = \(rows) ;\n"]++
    ["cols = \(cols) ;\n"]++
    ["f_width = array3d(ROWS,COLS,CONFIGS, \(array1d(width))) ;\n"]++
    ["f_height = array3d(ROWS,COLS,CONFIGS, \(array1d(width))) ;\n"]++
    ["% config = \(config) ;\n"]++
    ["% config_size = \(config_size);\n"]++
    ["% conf/size = \(sum(c in array1d(config))(c-1) / sum(c in array1d(config_size))(c-1)) ;\n"]++
    ["% median_cell_width = \(median_cell_width) ;\n"]++
    ["% colwidth = \(sum(colwidth)) ;\n"]++
    ["% rowheight = \(sum(rowheight)) ;\n"]++
    ["% +++ = \(sum(colwidth)+sum(rowheight)) ;\n"]
  ;

