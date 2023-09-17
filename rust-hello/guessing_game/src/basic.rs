pub fn test_iter() {
    let arr = [1, 2, 3, 4];
    for n in arr {
        println!("{}!", n);
    }
    println!("{}", arr.len());
    let v = vec![String::from("1"), String::from("2")];
    //
    // Vec / &'a Vec / &'a mut Vec 都实现了 IntoIterator trait
    // Vec::into_iter(self) 默认会把 v 和 v 中元素的所有权拿走. https://www.jdon.com/62799.html
    // 除非使用 &v，这样入参就是 into_iter(&self)
    for n in (&v).into_iter() {
        //  Equivalent to ```for n in &v```
        println!("{}!", n);
    }

    // 手动模拟 for
    match IntoIterator::into_iter(&v) {
        // 不会被拿走
        mut iter => loop {
            match iter.next() {
                Some(x) => {
                    println!("{}", x);
                }
                None => break,
            }
        },
    };
}

fn f1(s: String) -> String {
    let ss = String::from("world");
    println!("{},{}", s, ss);
    s // s的所有权移到函数外（s引用的内存空间被传来传去...
} // ss跳出作用域，释放 "world"

fn f2(s: &String) {
    let ss = String::from("world");
    println!("{},{}", s, ss);
}

// 每个[值]任意时刻只能有且仅有一个被称之为【所有者】的【变量】
// 当【所有者】超出{作用域} (scope)时，该[值]将被删除
// 不允许存在对堆中同一个内存的多个ref!
fn ownership() {
    let s1 = String::from("hello");
    let s2 = f1(s1); // 所有权从s1移动到f1参数，f1返回值的所有权移给s2
    f2(&s2);
    println!("{}", s2); // NOTE: println!()不会转移s2的所有权
} // s2出作用域，释放堆内存
  // s1出作用域（s1没有所有权，所以无任何影响）

fn calc_len(s: &mut String) -> usize {
    // ref 默认不可变，除非加 mut
    s.push_str(", world"); // mut 才可以
    s.len()
}

// https://www.runoob.com/rust/rust-ownership.html
pub fn mut_ref() -> String {
    let mut s1 = String::from("Hello");
    let s1ref = &mut s1; // 不可变引用，不能与可变引用同时存在
    println!("Non-mutable ref '{}'", s1ref);

    let s1mref = &mut s1; // 可变引用(可以装修)
    s1mref.push_str("_string");
    s1.push_str("_push_str_twice!");
    {
        let mut s11 = &s1; // 可变引用(可以换租)
                           // s11.push_str("fail"); // 不能装修
        let mut tmp = String::from("another string");
        s11 = &mut tmp;
        // s11.push_str("fail"); // 换租后，能装修的继续能，不能装修的继续不能
    }
    {
        let mut s12: &mut String = &mut s1; // 可变引用(可以装修或换租)
        let len = calc_len(s12); // ref 默认不可变，除非加 mut
        println!("The length of '{}' is {}", s12, len);
    }

    let hello = &s1[..5]; // [0, 5)
    let world = &s1[6..]; // [6, end)
    let s2 = s1.clone(); // Clone 深拷贝!!!
    let a = 12;
    let b = a; // 这是 Copy
    s1
}

pub fn slice_test() {
    let a = [1,2,3,4,5];
    let s = &a[1..3]; // slice! no ownership
    assert_eq!(s, &[2,3]);
}

fn first_word(s: &String) -> &str {
    let bytes = s.as_bytes();
    for (i, &item) in bytes.iter().enumerate() {
        if item == b' ' {
            return &s[..i];
        }
    }
    &s[..]
}
