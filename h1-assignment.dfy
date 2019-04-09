/**
    ©João Costa Seco, Eduardo Geraldo, CVS, FCT NOVA, MIEI 2019
 */


function unique(a:array<int>, l:int, h:int) : bool 
reads a
requires 0 <= l <= h <= a.Length
{ forall i,j :: (l <= i < h) && (i < j < h) ==> a[i] != a[j] }

function method contains(a:array<int>, n:int, e:int) : bool 
reads a
requires 0 <= n <= a.Length
{ e in a[..n] }

function isSet(a:array<int>, na:int) : bool
reads a
{ 0 <= na <= a.Length && unique(a, 0, na) }

method XorSet(a:array<int>, na:int, b:array<int>, nb:int) returns (z:array<int>, nz:int)
requires 0 <= na <= a.Length
requires 0 <= nb <= b.Length
requires isSet(a , na);
requires isSet(b, nb);
ensures isSet(z, nz)
ensures nz <= na || nz <= nb


{
    var i:int := 0;
}