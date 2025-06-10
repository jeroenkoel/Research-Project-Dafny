ghost predicate sameContent(a: seq<int>, b: seq<int>)
{
    multiset(a[..]) == multiset(b[..])
}

method selectionSort(v: array<int>)
    requires v.Length >= 1
    ensures sameContent(v[..], old(v[..]))
    ensures forall i, j :: 0 <= i < j < v.Length ==> v[i] <= v[j]
    modifies v
{
    var n := 0;
    while n < v.Length
        invariant 0 <= n <= v.Length
        invariant sameContent(v[..], old(v[..])) // making sure that at each iteration no new elements were introduced or entries got removed
        invariant forall i, j :: 0 <= i < n <= j < v.Length ==> v[i] <= v[j] // everyting on the left is smaller  than everything on the right
        invariant forall i, j :: 0 <= i < j < n ==> v[i] <= v[j] // the sorted part of the array is sorted in assending order
    {
        var min_index := n;
    	var i := n + 1;
        while i < v.Length
            invariant n + 1 <= i <= v.Length // making sure that i is correct at each iteration
            invariant n <= min_index < v.Length // making sure that we never get a min index that is either out of bounds or in the sorted part of the array
            invariant forall j :: n <= j < i ==> v[min_index] <= v[j] // our current min_index has the smallest value
        {
            if v[i] < v[min_index] {
                min_index := i;
            }
            i := i + 1;
        }
        var temp := v[n];
        v[n] := v[min_index];
        v[min_index] := temp;
        n := n + 1;
    }
}

method Main() {
    var sorted := new int[8][3, 6, 8, 1, 5, 2, 9, 3];
    selectionSort(sorted);
    var i := 0;
    while i < sorted.Length {
        print sorted[i];
        i := i + 1;
    }
}