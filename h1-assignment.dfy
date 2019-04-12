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
requires isSet(a , na)
requires isSet(b, nb)
ensures isSet(z, nz)
ensures nz <= z.Length <= na + nb
ensures 0 <= nz 
ensures forall f :: f in z[..nz] <==> (contains(a, na, f) && !contains(b, nb, f)) || (contains(b, nb, f) && !contains(a, na, f))
ensures forall f :: contains(a, na, f) && !contains(b, nb, f) ==> contains(z, nz, f)
ensures forall f :: contains(b, nb, f) && !contains(a, na, f) ==> contains(z, nz, f)


{
    var i:int := 0;
    nz := 0;
    z := new int[na + nb];

    while ( i < na)
    decreases na - i
    invariant 0 <= nz <= z.Length
    invariant isSet(z, nz)
    invariant nz <= na
    invariant nz <= i
    invariant 0 <= i <= na
    invariant forall f :: f in z[..nz] <==> (contains(a, i, f) && !contains(b, nb, f)) 
    invariant forall f :: f in z[..nz] ==>  contains(a, na, f)
    invariant forall f :: contains(a, na, f) && contains(b, nb, f) ==> !contains(z, nz, f)
    {
        
        if(!contains(b, nb, a[i])){
            z[nz] := a[i];
            assert forall f :: contains(z, nz, f) <==> contains(a, i, f) && !contains(b , nb, f);
            nz := nz + 1;
        }
        i := i + 1;
           
    }

    i := 0;
    var curr := nz;
    

    while ( i < nb)
    decreases nb - i
    invariant curr <= nz <= z.Length
    invariant isSet(z, nz)
    invariant nz <= nb + na
    invariant nz <= curr + i
    invariant 0 <= i <= nb
    invariant curr <= nz
    invariant forall f :: f in z[..nz] <==>  (contains(a, na, f) && !contains(b, nb, f)) || (contains(b, i, f) && !contains(a, na, f))
    invariant forall f :: f in b[..i] && !contains(a, na, f) ==> contains(z , nz, f)
    //invariant forall f :: f in a[..na] && !contains(b, nb, f) <==> contains(z , curr, f)
     //invariant forall f :: f in z[..nz] ==> (contains(b, nb, f) || contains(a, na, f)) && !(contains(a, na, f) && contains(b, nb, f))
    {
        if(!contains(z, nz, b[i]) && !contains(a, na, b[i])){
            z[nz] := b[i];
            assert forall f :: f in b[..i] && !contains(a, na, f) ==> contains(z , nz, f);

            nz := nz + 1;  
        }
        i := i + 1;
         
    }
    
}