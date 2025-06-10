package keyStore;

import java.util.ArrayList;
import java.util.List;

class exampleKeyStore {
    
    private myMap<String, Object> map;

    public exampleKeyStore() {
        this.map = new myMap<>();
    }

    public <T> void put(String key, Object value) {
        map.put(key, value);
    }

    public <T> Object get(String key) {
        return map.get(key);
    }

    public Object delete(String key) {
        return map.remove(key);
    }
}

class myMap<K extends Comparable<K>, V> {

    private List<Entry<K, V>> entries;

    public myMap() {
        this.entries = new ArrayList<>();
    }

    public void put(K key, V value) {
        for (int i = 0; i < entries.size(); i++) {
            if (this.entries.get(i).key.equals(key)) {
                this.entries.get(i).value = value;
                return;
            }
        }
        entries.add(new Entry<>(key, value));
    }

    public V get(K key) {
        for (int i = 0; i < entries.size(); i++) {
            if (this.entries.get(i).key.equals(key)) {
                return this.entries.get(i).value;
            }
        }
        return null;
    }

    public V remove(K key) {
        for (int i = 0; i < entries.size(); i++) {
            if (this.entries.get(i).key.equals(key)) {
                V v = this.entries.get(i).value;
                this.entries.remove(i);
                return v;
            }
        }
        return null;
    }

    static class Entry<K, V> {
        K key;
        V value;

        Entry(K key, V value) {
            this.key = key;
            this.value = value;
        }
    }
}