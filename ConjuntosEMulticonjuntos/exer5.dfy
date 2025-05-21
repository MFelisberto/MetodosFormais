ghost predicate Permutacao(a:seq<int>, b:seq<int>)
{
 multiset(a) == multiset(b)
}

ghost predicate OrdenadoEntre(a:array<int>, e:int, d:int)
 requires 0 <= e <= d <= a.Length
 reads a
{
 forall i,j ::e <= i <= j < d ==> a[i] <= a[j]
}

ghost predicate Ordenado(a:array<int>)
 reads a
{
 OrdenadoEntre(a,0,a.Length)
}

method BubbleSort(a:array<int>)
 modifies a
 ensures Ordenado(a)
 ensures Permutacao(a[..], old(a[..]))
 {
    var n := a.Length;
    var i := 0;
    
    while i < n
    {
        var swapped := false;
        var j := 0;
        
        while j < n - i - 1 
        {
            if a[j] > a[j+1]
            {
                a[j], a[j+1] := a[j+1], a[j];
                swapped := true;
                j := j + 1;
            }
        }
        
        if !swapped
        {
            break;
        }
        
        i := i + 1;
    }
 }
 
 



