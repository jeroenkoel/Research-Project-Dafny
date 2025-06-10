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
        map.put(5, "hello");
        _IOption<string> output = map.get(5);
        Console.WriteLine(output.dtor_value);

        map.put(4, "farewell");
        map.put(517, "not hello");
        map.put(10, "byebye");

        var nothing = map.get(15);
        if (nothing.is_None)
        {
            Console.WriteLine("Nothing is returned");
        }
        else
        {
            Console.WriteLine("something went wrong");
        }
    }
}