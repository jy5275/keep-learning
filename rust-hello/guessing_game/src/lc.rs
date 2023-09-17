// LifeCycle: https://kaisery.github.io/trpl-zh-cn/ch10-03-lifetime-syntax.html

// 返回引用的生命周期 = min(参数所引用的值的生命周期)
fn longest<'a>(x: &'a str, y: &'a str) -> &'a str {
    if x.len() > y.len() {
        x
    } else {
        y
    }
}

fn lct() {
    let string1 = String::from("abcd");
    let string2 = "xyz";

    let result = longest(string1.as_str(), string2);
    println!("The longest string is {}", result);
}
