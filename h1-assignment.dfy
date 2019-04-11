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
ensures forall j :: 0 < j < na ==> (contains(a, na, a[j]) && !contains(b, nb, a[j])) ==> contains(z, nz, a[j])
ensures forall j :: 0 < j < nb ==> (contains(b, nb, b[j]) && !contains(a, na, b[j])) ==> contains(z, nz, b[j])
ensures forall e :: e in z[..nz] ==> (contains(a, na, e) || contains(b, nb, e)) && !(contains(a, na, e) && contains(b, nb, e))


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
    //invariant 0 <= na <= n
    //invariant forall j :: 0 < j < na => contains(z, nz, a[j]) || !contains(b, nb, b[j])
    invariant forall e :: e in z[..nz] ==> (contains(a, na, e) || contains(b, nb, e)) && !(contains(a, na, e) && contains(b, nb, e))
    invariant forall f :: f in a[..i] ==> !contains(b, nb, f) ==> contains(z , nz, f)
    {
        // Arranjar forma de tirar a[i] !in z[..nz] (garantir que o i ainda nao esta no z)
        if(a[i]) !in b[..nb] && a[i] !in z[..nz]{
            z[nz] := a[i];
            assert forall f :: f in a[..i] ==> !contains(b, nb, f) ==> contains(z , nz, f);
            nz := nz + 1;
        }
        i := i + 1;
           
    }

    i := 0;
    var curr := nz;
    

    while ( i < nb)
    decreases nb - i
    invariant 0 <= nz <= z.Length
    invariant isSet(z, nz)
    invariant nz <= nb + na
    invariant nz <= i + na
    invariant 0 <= i <= nb
    invariant curr <= nz
    //invariant 0 <= na <= n
    //invariant forall j :: 0 < j < na => contains(z, nz, a[j]) || !contains(b, nb, b[j])
    invariant forall e :: e in z[..nz] ==> (contains(b, nb, e) || contains(a, na, e)) && !(contains(a, na, e) && contains(b, nb, e))
    invariant forall f :: f in a[..na] ==> !contains(b, nb, f) ==> contains(z , curr, f)
    invariant forall f :: f in b[..i] ==> !contains(a, na, f) ==> contains(z , nz, f)
    {
        // Arranjar forma de tirar a[i] !in z[..nz] (garantir que o i ainda nao esta no z)
        if(b[i]) !in a[..na] && b[i] !in z[..nz]{
            z[nz] := b[i];
            assert forall f :: f in b[..i] ==> !contains(a, na, f) ==> contains(z , nz, f);

            nz := nz + 1;  
        }
        i := i + 1;
         
    }
    
}