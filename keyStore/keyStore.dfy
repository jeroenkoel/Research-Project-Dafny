datatype Option<T> = None | Some(T)

class KeyStore {
    var entries : map<string, object>

    constructor() {
        entries := map[];
    }

    method get(key: string) returns(val: Option<object>)
        ensures (key in entries.Keys) ==> val == Some(entries[key])
        ensures (key !in entries.Keys) ==> val == None
    {
        if key in entries.Keys {
            val := Some(entries[key]);
        } else {
            val := None;
        }
    }

    function Put(store: map<string, object>, entry: map<string, object>): map<string, object>
        ensures forall k :: k in store || k in entry ==> k in Put(store, entry)
        ensures forall k :: k in entry ==> Put(store, entry)[k] == entry[k]
        ensures forall k :: k !in entry && k in store ==> Put(store, entry)[k] == store[k]
        ensures forall k :: k !in entry && k !in store ==> k !in Put(store, entry)
    {
        map x | x in (store.Keys + entry.Keys) :: if x in entry then entry[x] else store[x]
    }

    method put(key: string, value: object)
        modifies this
        ensures forall k :: k in old(entries) || k == key ==> k in entries
        ensures entries[key] == value
        ensures forall k :: k != key && k in old(entries) ==> entries[k] == old(entries[k])
        ensures forall k :: k != key && k !in old(entries) ==> k !in entries
    {
        var update := map[key := value];
        entries := Put(entries, update);
    }

    method delete(key: string) returns(val: Option<object>)
        modifies this
        ensures key in old(entries) ==> key !in entries
        ensures key !in old(entries).Keys ==> old(entries) == entries
        ensures forall k :: k != key && k in old(entries) ==> k in entries
        ensures forall k :: k != key && k in old(entries) ==> entries[k] == old(entries[k])
        ensures key in old(entries) ==> val == Some(old(entries[key]))
        ensures key !in old(entries) ==> val == None
    {
        if key in entries.Keys {
            val := Some(entries[key]);
            entries := map x | x in (entries.Keys - {key}) :: entries[x];
        } else {
            val := None;
        }
    } 
}

method Main() {}