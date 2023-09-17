use crate::enumt::{Area, Color, Rectangle};
use std::fmt::Debug;
use std::ops::Add;
use std::ops::Mul;

// i:i32 ====> T: TraitName
// Trait 其实是泛型的数据类型，Trait 限制了泛型所能代表的类型，正如数据类型限制了变量所能存放的数据
fn double<T>(i: T) -> T
where
    T: Add<Output = T> + Clone + Copy,
{
    i + i
}

fn double_2<T: Add<Output = T> + Clone + Copy>(i: T) -> T {
    i + i
}

trait Eatable {
    fn eat_me(&self);
}

#[derive(Debug)]
struct Food<T>(T);

impl<T: Debug> Eatable for Food<T> {
    fn eat_me(&self) {
        println!("Eating: {:?}", self);
    }
}

#[derive(Debug)]
enum Shape<T> {
    Square(T),
    Rectangle(T, T),
}

impl<T> Area<T> for Shape<T>
where
    T: Debug + Mul<Output = T> + Copy + Clone,
{
    fn get_size(&self) -> T {
        match *self {
            Shape::Square(e) => e * e,
            Shape::Rectangle(a, b) => a * b,
        }
    }
}

pub fn gent() {
    println!("double result={}", double_2(221));
    let c = Color::new(255, 255, 255);
    let f = Food(c);
    // f.eat_me(); // Food(Color)'s trait bounds aren't satisfied for eat_me fn

    let mut shapes: Vec<&dyn Area<_>> = vec![];
    shapes.push(&Shape::Rectangle(10, 20));
    shapes.push(&Shape::Square(3));
    println!("shape 0: {}", shapes[0].get_size());
}
