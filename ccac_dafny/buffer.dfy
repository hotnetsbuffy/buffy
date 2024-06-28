module Buffer{
  type Pkt = int
  type Buf = seq<Pkt>

  function head(buf: Buf): Pkt{
    if|buf| == 0 then 0 else buf[0]
  }

  function tail(buf: Buf): Buf {
    if |buf| == 0 then buf else buf[1..]
  }

  function filter(buf: Buf, f: int): Buf{
    if |buf| <= 0 then []
    else if buf[0] == f then buf[0..1] + filter(tail(buf), f)
    else filter(tail(buf),f)
  }

  function backlog(buf: Buf): Pkt{
    |buf|
  }

  function move(a: Buf, b: Buf): (Buf, Buf) {
    (tail(a), b + [head(a)])
  }

    function moveval(a: Buf, b: Buf, c:Pkt): (Buf, Buf) {
    (tail(a), b + [c])
  }


  method moven(a: Buf, b: Buf, n: int) returns (y: Buf, z:Buf )
  requires n >= 0
  requires backlog(a) >= n
  ensures backlog(z) == backlog(b) + n
  ensures backlog(y) == backlog(a) - n
   {
    y := a;
    z := b;
    for i := 0 to n 
        invariant 0 <= i <= n
        invariant backlog(z) == backlog(b) + i
        invariant backlog(y) == backlog(a) - i
        {
      
       var (c,d) := move(y, z);
       y := c;
       z := d;
    }
    return y, z;
  }



  function empty(buf: Buf): Pkt{
    if|buf| == 0 then 0 else buf[0]
  }

}
