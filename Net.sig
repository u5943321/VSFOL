signature Net = 
sig
type 'a tnet
val empty: 'a tnet
val match: term -> 'a tnet -> 'a list
val tinsert: term * 'a -> 'a tnet -> 'a tnet
type 'a fnet
val fempty: fconv fnet
val fmatch: form -> fconv fnet -> fconv list
val finsert: form * fconv -> fconv fnet -> fconv fnet



datatype flabel0
    = Q0 of string
    | Cn0 of string
    | fV0
    | Pr0 of string
    | tV0
    | tFn0 of string


datatype 'a fnet0
    = fleaf of 'a list
    | fnode of (flabel0 * 'a fnet0) list;

val show_net: 'a fnet -> 'a fnet0
end
