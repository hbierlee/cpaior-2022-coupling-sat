%%% Boolean Encoding Scheme
include "options.mzn";
include "sat_annotations.mzn";
include "views.mzn";

% include "binary_adders.mzn";

include "pbify.mzn";
include "channel_encodings.mzn";
include "pblib.mzn";

include "unary_encode.mzn";
include "order_encode.mzn";
include "binary_encode.mzn";

include "redefs_int_unary.mzn";
include "redefs_int_order.mzn";
include "redefs_int_binary.mzn";

% FlatZinc builtins
include "redefs_bool.mzn";
include "redefs_bool_imp.mzn";
include "redefs_float.mzn";
include "redefs_int.mzn";
% TODO [!] don't forget to re-enable this
% include "redefs_int_imp.mzn";
include "redefs_set.mzn";
include "redefs_search.mzn";
