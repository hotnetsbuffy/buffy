include "params.dfy"

type Pkt = int
type Buf = seq<Pkt>
type BufIdx = int
type Time = int
type Metric = int
type BufStream = seq<Buf>
type MetricStream = seq<Metric>

function sum(s: seq<int>, i: int): int
  requires i >= 0 && i < |s|
{
  if |s| == 0 then 0
  else if i == 0 then s[0]
  else s[i] + sum(s, i - 1)
}

function btoi(b: bool): int{
  if b then 1 else 0
}

predicate valid_bi(i: BufIdx){
  i >= 0 && i < NUM_IN_BUFS
}

function find(vals: seq<int>, val: int): bool
requires |vals| <= 3 
{
  if |vals| == 0 then false
  else if |vals| == 1 then vals[0] == val
  else if |vals| == 2 then (vals[0] == val || vals[1] == val)
  else if |vals| == 3 then (vals[0] == val || vals[1] == val || vals[2] == val)
  else false
}