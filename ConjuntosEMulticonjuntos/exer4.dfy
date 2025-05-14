method TrocaElementos(a: array<int>, i: int, j: int)
    // pré
    requires 0 <= i < a.Length && 0 <= j < a.Length
    
    modifies a
    
    // o array a é IGUAL ao array original
    // mas com os elementos i e j trocados
    // pós
    ensures a[j] == old(a[i]) && a[i] == old(a[j])
    ensures forall k :: 0<=k<a.Length && k!=i && k!=j ==> a[k] == old(a[k])
    {
        var temp := a[i];
        a[i] := a[j];
        a[j] := temp;
        // OU -> versao curta
        // a[i], a[j] := a[j], a[i];
    }

method Main() 
{
 var a := new int[] [1, 2, 3, 4, 5];
 assert a[..] == [1, 2, 3, 4, 5];
 ghost var antes := a; // so pra especificao
 TrocaElementos(a, 0, 3);
 assert a[..] == [4, 2, 3, 1, 5];

 assert multiset(a[..]) == multiset(antes[..]);


}