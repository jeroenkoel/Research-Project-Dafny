package keyStore;

public class Main {
    
    public static void main(String[] args) {
        exampleKeyStore test = new exampleKeyStore();
        test.put("hello", 14);
        test.put("hello", 40);
        test.put("new", true);
        System.out.println(test.get("new"));
        System.out.println(test.delete("new"));
        System.out.println(test.get("new"));
        System.out.println(test.get("hello"));
    }
}
