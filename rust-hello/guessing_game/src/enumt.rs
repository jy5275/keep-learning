use std::{cell::Ref, fmt::Debug};
use clap::builder::Str;

enum Json {
    Null,
    Boolean(bool),
    Number(f64),
    String(String),
    Array(Vec<Json>),
}

#[derive(Clone, Debug)]
enum IpAddrType {
    // like union in C++
    V4(u8, u8, u8, u8),
    V6(String),
}

pub fn enumt() {
    let home = IpAddrType::V4(127, 0, 0, 1);
    let loopback = IpAddrType::V6(String::from("::1"));
    match &home {
        IpAddrType::V4(_, a, b, c) => println!("IPV4 machine: n{}-{}-{}", a, b, c),
        IpAddrType::V6(s) => println!("IPV6 machine: {}", s),   // 这里的 String 也会 move!!!
    };

    let random_ip = home.clone();
    if let IpAddrType::V4(_, m2, m3, m4) = random_ip {
        println!("random_ip is an ipv4 addr n{}-{}-{}", m2, m3, m4);
    }

    // let-else, 声明变量同时处理错误，相当于 if-let 的反式写法
    let IpAddrType::V4(_, n2, n3, n4) = random_ip else {
        println!("fewfew");
        return;
    };
    println!("random_ip is an ipv4 addr n{}-{}-{}", n2, n3, n4);
}

#[derive(Copy, Clone)]
enum Week {
    Monday = 1,
    Tuesday,
    Wednesday,
    Thursday,
    Friday,
    Saturday,
    Sunday,
}

impl Week {
    fn is_weekend(&self) -> bool {
        if (*self as u8) > 5 {
            return true;
        }
        false
    }
}

// ============================ struct, trait ============================
#[derive(Debug, Clone, Copy)]
pub struct Color(i32, i32, i32);    // tuple!
impl Color {
    pub fn new(a: i32, b: i32, c: i32) -> Color {
        Color(a, b, c)
    }
}

pub struct Point(i32, i32, i32);

pub trait Area<T>: Debug {
    fn get_size(&self) -> T;
    // fn larger_than(&self, o: &dyn Area<T>) -> bool {
    //     self.get_size() > o.get_size()
    // }
}

#[derive(Debug, Clone)] // 类似 go 里面的 fmt.Print("%v", rect)
pub struct Rectangle {
    width: u32,
    length: u32,
    name: Option<String>,
}

impl Rectangle {
    fn perimeter(&self) -> u32 {
        // 实际调用时不需要填self参数
        (self.length + self.width) * 2
    }
    fn can_hold(&self, other: &Rectangle) -> bool {
        self.width > other.width && self.length > other.length
    }
    pub fn new(width: u32, length: u32) -> Rectangle {
        // 关联函数：没有 self 参数，不是方法，类似 String::from，通常用于 constructor
        Rectangle {
            width,
            length,
            name: Some(String::from("rectangle"))
        }
    }
    fn get_name_and_consume(self) -> String {   // 字段被偷导致整个 obj 被偷走！
        self.name.unwrap_or(String::from("empty"))
    }
}

impl Area<u32> for Rectangle {
    fn get_size(&self) -> u32 {
        self.width * self.length
    }
}

/*
      Area Trait Object Type -----------------------  Real Type
               |                                    |
               |                                    |
               \/                                   \/
    -------------------------              -------------------
   |         vtable          |            |     Rectangle     |
   |-------------------------|            |-------------------|
   |   get_size      |   *   |            |     width:u32     |
   |-------------------------|            |-------------------|
   |    fn_2         |   *   |            |    length:u32     |
    -------------------------             |-------------------|
                                          |    name:String    |
                                           -------------------
*/
pub fn rectt() {
    let rect = Rectangle::new(30, 50);
    // let name = rect.get_name_and_consume();  // 会把 rect 偷走！
    let rref: &dyn Area<_> = &rect;
    let mut shapes: Vec<&dyn Area<_>> = vec![rref];

    println!("Area {:#?} is {}", rref, rref.get_size());

    let Rectangle {
        width,
        length,
        ref name,
    } = rect;
    println!(
        "R2 w={}, l={}, name={}",
        width,
        length,
        name.as_ref().unwrap()
    );
    println!(
        "R1 w={}, l={}, name={}",
        rect.width,
        rect.length,
        rect.name.unwrap()
    );
}

pub fn copyt() {
    let black = Color(0, 0, 0);
    let origin = Point(0, 0, 0);
    let b2 = black; // copy
    let b3 = black.clone(); // clone (deep copy)
    println!("{:#?}, {:#?}", b2, black);
}
