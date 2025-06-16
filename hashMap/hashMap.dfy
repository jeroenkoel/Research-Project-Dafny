module Hashing {

    class Entry<K(==), V> {
        const key: K
        const value: V

        constructor(k: K, v: V) 
            ensures key == k 
            ensures value == v
        {
            key := k;
            value := v;
        }
    }

    datatype Option<T> = Some(value: T) | None

    class HashMap<K(==), V> {

        const SIZE: int := 512
        var table: array<seq<Entry<K, V>>>
        const hashFnc: K -> int

        constructor(fnc: K -> int)
            ensures table.Length == SIZE
            ensures forall i :: 0 <= i < SIZE ==> table[i] == []
            ensures hashFnc == fnc
        {
            table := new seq<Entry<K, V>>[SIZE](i => []);
            hashFnc := fnc;
        }

        ghost predicate keyUniquenessChain(chain: seq<Entry<K, V>>)
        {
            forall i, j :: 0 <= i < |chain| && 0 <= j < |chain| && i != j ==> chain[i].key != chain[j].key
        }

        ghost predicate keyUniquenessStrong(list: seq<seq<Entry<K, V>>>)
        {
            forall i :: 0 <= i < |list| ==> keyUniquenessChain(list[i])
        }

        ghost predicate keyMapsToHashedIndex(list: array<seq<Entry<K, V>>>)
            reads list
        {
            forall i :: 0 <= i < list.Length ==> forall e :: e in list[i] ==> getIndex(e.key) == i
        }

        lemma determinstic(func: K -> int, key1: K, key2: K)
            ensures key1 == key2 ==> func(key1) == func(key2)
        {

        }

        lemma keyNotInHashedChainNotInTable(key: K) 
            requires table.Length == SIZE
            requires key !in keysOfChain(table[getIndex(key)])
            requires keyMapsToHashedIndex(table)
            ensures forall e :: e in table[..] ==> key !in keysOfChain(e)
            ensures key !in keysOfTable(table[..])
        {
            keysOfTableCorrect(table[..]);
        }

        function getIndex(key: K): int
            ensures 0 <= getIndex(key) < SIZE
        {
            var hashCode := hashFnc(key);    
            hashCode % SIZE
        }

        function keysOfChain(chain: seq<Entry<K, V>>): seq<K>
            ensures forall e :: e in keysOfChain(chain) ==> exists e2 :: e2 in chain && e == e2.key
            ensures forall e :: e in chain ==> e.key in keysOfChain(chain) 
        {
            if |chain| == 0 then []
            else [chain[0].key] + keysOfChain(chain[1..])
        }

        function keysOfTable(list: seq<seq<Entry<K, V>>>): seq<K> 
        {
            if |list| == 0 then []
            else keysOfChain(list[0]) + keysOfTable(list[1..])
        }

        lemma keysOfTableCorrect(list: seq<seq<Entry<K, V>>>)
            ensures forall e1 :: e1 in list ==> forall e2 :: e2 in keysOfChain(e1) ==> e2 in keysOfTable(list)
            ensures forall e1 :: e1 in keysOfTable(list) ==> exists e2 :: e2 in list && e1 in keysOfChain(e2)
        {
            assert forall e1 :: e1 in keysOfTable(list) ==> exists e2 :: e2 in list && e1 in keysOfChain(e2);
        }

        function getEntryChain(chain: seq<Entry<K, V>>, key: K): V
            requires key in keysOfChain(chain)
            requires keyUniquenessChain(chain)
            ensures forall e :: e in chain && e.key == key ==> getEntryChain(chain, key) == e.value
        {
            if |chain| == 1 then chain[0].value
            else if chain[0].key == key then chain[0].value 
            else getEntryChain(chain[1..], key)
        }

        method get(key: K) returns(out: Option<V>)
            requires table.Length == SIZE
            requires keyUniquenessStrong(table[..])
            requires keyMapsToHashedIndex(table)
            ensures table.Length == SIZE 
            ensures keyUniquenessStrong(table[..])
            ensures keyMapsToHashedIndex(table)
            ensures key in keysOfTable(table[..]) ==> key in keysOfChain(table[getIndex(key)])
            ensures key in keysOfTable(table[..]) ==> out == Some(getEntryChain(table[getIndex(key)], key))
            ensures key !in keysOfTable(table[..]) ==> out.None?
        {
            var index := getIndex(key);
            var chain := table[index];
            if key in keysOfChain(chain) {
                keysOfTableCorrect(table[..]);
                out := Some(getEntryChain(chain, key));
            } else {
                keyNotInHashedChainNotInTable(key);
                out := None;
            }
                
        }

        function replaceKey(entry: Entry<K, V>, chain: seq<Entry<K, V>>): seq<Entry<K, V>>
            requires entry.key in keysOfChain(chain)
            requires keyUniquenessChain(chain)
            ensures keyUniquenessChain(replaceKey(entry, chain))
            ensures entry in replaceKey(entry, chain)
            ensures forall e :: e in chain ==> e.key in keysOfChain(replaceKey(entry, chain))
            ensures forall e :: e in replaceKey(entry, chain) ==> e.key in keysOfChain(chain)
            ensures forall e :: e in chain && e.key != entry.key ==> e in replaceKey(entry, chain)
            ensures forall e :: e in replaceKey(entry, chain) && e != entry ==> e in chain 
        {
            if |chain| == 1 then [entry]
            else if chain[0].key == entry.key then [entry] + chain[1..]
            else [chain[0]] + replaceKey(entry, chain[1..])
        }

        function addKey(entry: Entry<K, V>, chain: seq<Entry<K, V>>): seq<Entry<K, V>>
            requires entry.key !in keysOfChain(chain)
            requires keyUniquenessChain(chain)
            ensures keyUniquenessChain(addKey(entry, chain))
            ensures entry.key in keysOfChain(addKey(entry, chain))
            ensures forall e :: e in chain ==> e in addKey(entry, chain)
            ensures forall e :: e in addKey(entry, chain) && e != entry ==> e in chain
        {
            chain + [entry]
        }

        method put(key: K, value: V)
            requires table.Length == SIZE
            requires keyUniquenessStrong(table[..])
            requires keyMapsToHashedIndex(table)
            ensures table.Length == SIZE
            ensures keyUniquenessStrong(table[..])
            ensures keyMapsToHashedIndex(table)
            ensures forall e :: 0 <= e < SIZE && e != getIndex(key) ==> old(table[e]) == table[e] 
            ensures key in keysOfTable(table[..])
            ensures key in keysOfChain(table[getIndex(key)]) 
            ensures value == getEntryChain(table[getIndex(key)], key)
            modifies table
        {
            var index := getIndex(key);
            var chain := table[index];
            var ent := new Entry(key, value);
            if key in keysOfChain(chain) {
                table[index] := replaceKey(ent, chain);
                keysOfTableCorrect(table[..]);
            } else {
                table[index] := addKey(ent, chain);
                keysOfTableCorrect(table[..]);
            }
        }

        function deleteKey(key: K, chain: seq<Entry<K, V>>): seq<Entry<K, V>>
            requires key in keysOfChain(chain)
            requires keyUniquenessChain(chain)
            ensures keyUniquenessChain(deleteKey(key, chain))
            ensures forall e :: e in chain && e.key != key ==> e in deleteKey(key, chain)
            ensures forall e :: e in deleteKey(key, chain) ==> e in chain && e.key != key
        {
            if |chain| == 1 then []
            else if chain[0].key == key then chain[1..]
            else [chain[0]] + deleteKey(key, chain[1..])
        }

        method delete(key: K) returns(out: Option<V>)
            requires table.Length == SIZE
            requires keyUniquenessStrong(table[..])
            requires keyMapsToHashedIndex(table)
            ensures table.Length == SIZE
            ensures keyUniquenessStrong(table[..]) 
            ensures keyMapsToHashedIndex(table)
            ensures forall e :: 0 <= e < SIZE && e != getIndex(key) ==> old(table[e]) == table[e] 
            ensures key in keysOfTable(old(table[..])) ==> key !in keysOfTable(table[..])
            ensures key !in keysOfTable(old(table[..])) ==> table == old(table)
            ensures key in keysOfTable(old(table[..])) ==> key in keysOfChain(old(table[getIndex(key)]))
            ensures key in keysOfTable(old(table[..])) ==> out == Some(getEntryChain(old(table[getIndex(key)]), key))
            ensures key !in keysOfTable(old(table[..])) ==> key !in keysOfChain(old(table[getIndex(key)])) 
            ensures key !in keysOfTable(old(table[..])) ==> out.None?
            modifies table
        {
            var index := getIndex(key);
            var chain := table[index];
            if key in keysOfChain(chain) {
                keysOfTableCorrect(table[..]);
                out := Some(getEntryChain(chain, key));
                table[index] := deleteKey(key, chain);
                keyNotInHashedChainNotInTable(key);
            } else {
                keyNotInHashedChainNotInTable(key);
                out := None;
            }
        }
    }

}