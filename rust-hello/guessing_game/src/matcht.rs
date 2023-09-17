fn m1() {
    let x = (11, 22);
    match x {
        (22, a) => println!("(22, {})", a),   // 匹配失败
        (a, 11) => println!("({}, 11)", a),   // 匹配失败
        (a, b) => println!("({}, {})", a, b), // 匹配成功，停止匹配
    }
}

fn plus_one(x: Option<i32>) -> Option<i32> {
    let val = x?;
    Some(val + 1)
}

fn m2() {
    let five = Some(5);
    let six = plus_one(five);
    let sum = five.unwrap() + six.unwrap();

    let n = plus_one(None);
    let v = Some(9u8);
    match v {
        Some(1) | Some(2) => println!("one-two"),
        Some(3) | Some(4) => println!("three-four"),
        Some(5) | Some(6) => println!("five-six"),
        Some(7) => println!("seven"),
        Some(x) => println!("other val: {}", x), // hit
        None => println!("None!"),
        _ => (), // never match
    }
}

fn m3(b: bool) {
    let mut x = (0, 22);
    if b {
        x.0 = 123;
    }
    if let (123, b) = x {
        // refutable, 匹配成功，因此执行大括号内的代码, if let是独立作用域，变量a b只在大括号中有效
        println!("12,{}", b);
    }
}

pub fn matcht() {}
