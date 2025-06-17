using System;

namespace hashMap;

using System.Numerics;
using Hashing;

public class test
{
    public void create()
    {
        var tab = new HashMap<int, string>();
        Func<int, BigInteger> hashFunction = key => new BigInteger(key);
        tab.__ctor(hashFunction);
    }
}

class Maain
{
    public static void Main(string[] args)
    {
        var map = new HashMap<int, string>();
        Func<int, BigInteger> hashFunction = key => new BigInteger(key);
        map.__ctor(hashFunction);

        // creating the variables and with that also tests put
        map.put(5, "hello");
        map.put(4, "farewell");
        map.put(517, "not hello");
        map.put(10, "byebye");

        // test 1: check if get returns nothing if no value exists at its key
        var test1 = map.get(15);
        if (test1.is_None)
        {
            Console.WriteLine(true);
        }
        else
        {
            Console.WriteLine(false);
        }

        // test 2: check if a get with a value attached to the key returns that value
        var test2 = map.get(10);
        if (test2.is_Some && test2.dtor_value == "byebye")
        {
            Console.WriteLine(true);
        }
        else
        {
            Console.WriteLine(false);
        }

        // test 3: see if delete key actually deletes the key
        map.delete(10);
        var test3 = map.get(10);
        if (test3.is_None)
        {
            Console.WriteLine(true);
        }
        else
        {
            Console.WriteLine(false);
        }

        map.put(0, ":)");
        map.put(512, ":(");

        // test 4: check if both keys exist in the end as they are on the same spot
        var test4_1 = map.get(0);
        var test4_2 = map.get(512);
        if (test4_1.is_Some && test4_2.is_Some && test4_1.dtor_value == ":)" && test4_2.dtor_value == ":(")
        {
            Console.WriteLine(true);
        }
        else
        {
            Console.WriteLine(false);
        }
    }
}