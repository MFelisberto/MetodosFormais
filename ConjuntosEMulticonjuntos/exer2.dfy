// Explique com suas palavras o que cada asserção 
// descrita no seguinte código significa:

// n -> posição do elemento
// e -> elemento a ser inserido
// modifies a -> o array a pode ser modificado
method FazAlgo(a: array<int>, n: int, e: int)
 // n é maior ou igual a 0 e menor que o tamanho do array a
 requires 0 <= n < a.Length
 // a pode ser modificado
 modifies a
 // garante que o array a[n] é igual a e
 // e que o array a[..n+1] é igual a a[..n] + [e]
 ensures multiset(a[..n+1]) == multiset(a[..n]) + multiset{e}
{
 a[n] := e;
 assert a[..n+1] == a[..n] + [e];
}
