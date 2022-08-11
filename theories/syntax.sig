action : Type
value : Type
gType : Type
endpoint : Type
dir : Type
list : Functor
ch : Type

GEnd : gType
GRec : (gType -> gType) -> gType
GMsg : action -> value -> gType -> gType
GBranch : action -> "list" (gType) -> gType

EEnd : endpoint
ERec : (endpoint -> endpoint) -> endpoint
EMsg : dir -> ch -> value -> endpoint ->  endpoint
EBranch : dir -> ch -> "list" (endpoint) -> endpoint
