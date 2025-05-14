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
 ensures Ordenado(a)
 ensures Permutacao(a[..], old(a[..]))
 
 modifies a





// def bubble_sort(arr):
method bubbleSort(arr:array<int>)
  // n = len(arr)0
  var n := arr.Length

  // for i in range(n):
  // forall k: int :: 0 <= k < a.Length ==> 0 < a[k]
  forall i: 0 <= i < n ==> 0 < arr[i]
    invariant
    // for j in range(0, n-i-1):
    forall j: 0 <= j < n-i-1 ==> 0 < arr[j]
        invariant
        // if arr[j] > arr[j+1]:
        if arr[j] > arr[j+1]
            arr[j], arr[j+1] := arr[j+1], arr[j]
