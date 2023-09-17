use crate::basic::{mut_ref, test_iter};
use rand::Rng;
use std::cmp::Ordering;
use std::io; // prelude
use std::error::Error;
use crate::enumt::rectt;

mod basic;
mod enumt;
mod gen;
mod lc;
mod matcht;
mod net;

const MAX_NUM: u32 = 100_000;

fn guess_num() {
    let secret_number = rand::thread_rng().gen_range(1, MAX_NUM);

    loop {
        println!("Guess");
        let mut guess = String::new();
        io::stdin().read_line(&mut guess).expect("failed to read");

        let guess: u32 = match guess.trim().parse() {
            Ok(num) => num,
            Err(_) => continue,
            // expect("failed to parse guess string");
        };

        match guess.cmp(&secret_number) {
            Ordering::Less => println!("Too small"), // arm
            Ordering::Greater => println!("Too big"),
            Ordering::Equal => {
                println!("You win");
                break;
            }
        }
    }
}

fn hello_rust() {
    println!("Hello");
    let mut input = String::new();
    io::stdin().read_line(&mut input).expect("failed to read");
    println!("Your raw input is {:?}", input);
    let num: usize = input.trim().parse().expect("input is not a num!");
    println!("Your input is {}", num);
    println!("PI = {1:.0$}", num, std::f64::consts::PI);
}

fn main() {
    // test_iter();
    // hello_rust()
    rectt();
}
