#[macro_use]
extern crate assert_float_eq;

fn hello_world() {
    println!("Hello, world!");
    // `println!` is a macro.
}

// --------------------------------------------------------------------------------

fn variables() {
    let x: i32 = 10;
    println!("x: {x}");
    // x = 20;  // ERROR: variables are by default immutable.

    let mut x: i32 = 10; // Can shadow variables.
    println!("x: {x}");
    x = 20; // This is ok because `x` is mutable now.
    println!("x: {x}");
    // x = "hey";  // ERROR: type mismatch.
    let x: String = String::from("hey"); // Redeclare `x` to be a string is ok.
    println!("x: {x}");
    println!("x: {:?}", x); // Print debug info.
    println!("x: {:#?}", x); // Pretty-prints the debug info (line breaks for arrays etc.).
    println!("x: {x:?}"); // Or like this.
                          // `structs` can support the debug representation with '#{derive Debug}'.
}

// --------------------------------------------------------------------------------

fn values() {
    // Signed and unsigned integers: `i32`, `u64`, etc.: `1_000`, `123_i64`
    // Use `u32` or `u64` for list indices.
    // Floating numbers: `f32` and `f64`: `1.2e20`, `2_f32`

    // Sizes are usually inferred for integers and floating numbers.

    // `char` is just `i32`. Strings are not a collection of `char`s.

    // `bool` values are `true` and `false`. They are not aliases to `1` and `0`.

    fn takes_u32(x: u32) {
        println!("u32: {x}");
    }

    fn takes_i8(x: i8) {
        println!("i8: {x}");
    }

    let mut _x = 10;
    takes_i8(_x); // Compiler infers `x` as `i8`.
    _x = 20;
    // _x = 1024;  // ERROR: 1024 is out of range of `i8`.
    // takes_u32(_x);  // ERROR: Type mismatch.
    takes_u32(_x as u32); // A couple of type casting operations exist. See https://stackoverflow.com/a/28280042.
}

// --------------------------------------------------------------------------------
// Exercise: Fibonacci.

#[allow(unused)]
fn fib(n: u32) -> u32 {
    if n <= 2 {
        1
    } else {
        fib(n - 1) + fib(n - 2)
    }
    // Returns the last expression in a block.
    // Note that the line does NOT end with a `;`:
    // That will implicitly add a null expression `()`
    // messing up the return value.
}

#[test]
fn test_fib() {
    assert_eq!(fib(20), 6765);
}

// --------------------------------------------------------------------------------

fn loops() {
    for i in 2..5 {
        println!("234: {i}")
    }
    for i in 2..=4 {
        println!("234: {i}")
    }
    for i in [2, 3, 4] {
        println!("234: {i}")
    }

    // `loop` for infinite loops.
    let mut i = 0;
    let x = loop {
        i += 1;
        if i > 5 {
            break i;
        }
        if i % 2 == 0 {
            continue;
        }
        println!("135: {i}");
    };
    println!("x: {x}");

    // Labeled loops:
    'outer: for i in 1..10 {
        for j in 2..4 {
            println!("i = {i}, j = {j}");
            break 'outer;
        }
    }
}

// --------------------------------------------------------------------------------

fn macros() {
    // Macros are "hygengic" in Rust.

    // Commonly used built-in macros:
    //
    // -   `println!(format, ..)`
    // -   `format!(format, ..)`
    // -   `dbg!(expression)`
    // -   `todo!(message)`: If executed, will panic and evaluate to an "any" type.
    // -   `unreachable!()`: If executed, will panic.

    let x = 3;
    println!("{}", 5 + dbg!(x)); // 5 + 3 = 8.
}

// --------------------------------------------------------------------------------
// Exercise: Collatz Length.

// Determine the length of the collatz sequence beginning at `n`.
#[allow(unused)]
fn collatz_length(mut n: i32) -> u32 {
    let mut i = 1;
    while n != 1 {
        n = if n % 2 == 0 { n / 2 } else { 3 * n + 1 };
        i += 1;
    }
    i
}

#[test]
fn test_collatz_length() {
    assert_eq!(collatz_length(11), 15);
}

// --------------------------------------------------------------------------------

fn arrays() {
    // Arrays have fixed lengths.
    let mut a: [i8; 10] = [42; 10];
    a[5] = 0;
    println!("a: {a:?}");

    // Tuples are anonymous structs.
    let t = (7, true);
    println!("{} is 7 and {} is true", t.0, t.1);
    println!("t is {t:?}");

    // Tuple unpacking.
    let pair = (3, 5);
    let (left, right) = pair;
    println!("left = {left}, right = {right}");

    let tuple = (3, 5, 7, 8);
    let (first, second, ..) = tuple;
    println!("first = {first}, second = {second}");

    let arr = [3, 5, 7, 8];
    let [first, rest @ ..] = arr;
    println!("first = {first}, rest = {rest:?}");
}

// --------------------------------------------------------------------------------
// Exercise: Transpose.

#[allow(unused)]
fn transpose(matrix: [[i32; 3]; 3]) -> [[i32; 3]; 3] {
    let mut res = matrix;
    for (i, row) in matrix.iter().enumerate() {
        for (j, cell) in row.iter().enumerate() {
            res[j][i] = *cell;
        }
    }
    res
}

#[test]
fn test_transpose() {
    let matrix = [
        [101, 102, 103], //
        [201, 202, 203],
        [301, 302, 303],
    ];
    let transposed = transpose(matrix);
    assert_eq!(
        transposed,
        [
            [101, 201, 301], //
            [102, 202, 302],
            [103, 203, 303],
        ]
    );
}

// --------------------------------------------------------------------------------

fn references() {
    #![allow(unused_assignments)]
    // Use `&` and `*` to reference or dereference a value.
    //
    let a = 'a';
    let mut b = 'b';
    let r: &char = &a;
    println!("*r should be a: {}", *r);
    // r = &b;  // ERROR: `r` is immutable.
    let mut r: &char = &a;
    r = &b;
    println!("*r should be b: {}", *r);
    // *r = 'x';  // ERROR: `r` is not a mutable/exclusive reference.
    let r = &mut b;
    *r = 'x';
    println!("b should be x: {}", b);
}

// --------------------------------------------------------------------------------

fn slices() {
    let mut a = [10, 20, 30, 40, 50, 60];
    println!("a: {a:?}");
    let s: &mut [i32] = &mut a[2..4];
    s[0] = 0;
    println!("s: {s:?}, len: {}", s.len());
    println!("a: {a:?}");

    // The length of a slice can vary.
    let end = 4;
    let s = &mut a[..end];
    println!("s.len: {}", s.len());
}

// --------------------------------------------------------------------------------

fn strings() {
    // Strings are slices. A "string silce" is written `&str`.
    // `&str` is an immutable reference to a string slice.
    // `String` is a mutable string buffer.

    let s: &str = "hello 世界";
    // s[2]  // NOTE: This is dangerous,
    //       // because you could index into the middle of an UTF-8 code.
    //       // `&str` is a slice of bytes,
    //       // and a character can take multiple bytes in UTF-7.

    for chara in s.chars() {
        println!("{chara}");
    }

    let start = s
        .find("世") //
        .unwrap(); // Ignore errors if any.
    let s1 = &s[start..];
    println!(
        "the character following 世 is {}",
        s1.chars().skip(1).next().unwrap()
    );
}

// --------------------------------------------------------------------------------
// Exercise: Geometry.

// Calculate the magnitude of a vector by summing the squares of its coordinates
// and taking the square root. Use the `sqrt()` method to calculate the square
// root, like `v.sqrt()`.
#[allow(unused)]
fn magnitude(vector: &[f64]) -> f64 {
    let mut res = 0.0;
    for n in vector {
        res += n * n;
    }
    res.sqrt()
}

// Normalize a vector by calculating its magnitude and dividing all of its
// coordinates by that magnitude.
#[allow(unused)]
fn normalize(vector: &mut [f64]) {
    let mag = magnitude(vector);
    for n in vector {
        *n /= mag;
    }
}

#[test]
fn test_geometry() {
    assert_eq!(magnitude(&[0.0, 1.0, 0.0]), 1.0);

    let mut v = [1.0, 2.0, 9.0];
    assert_float_relative_eq!(magnitude(&v), 9.2, /*tolarence=*/ 0.1);
    normalize(&mut v);
    assert_float_relative_eq!(magnitude(&v), 1.0);
}

// --------------------------------------------------------------------------------

fn defining_types() {
    struct Person {
        name: String,
        age: u8,
    }
    let peter = Person {
        name: String::from("Peter"),
        age: 27,
    };
    println!("{} is {} years old", peter.name, peter.age);

    // Initializing using existing data.
    let jackie = Person {
        name: String::from("Jackie"),
        ..peter
    };
    println!("{} is also {} years old", jackie.name, jackie.age);

    // A "tuple struct".
    struct Point(i32, i32);
    let Point(left, right) = Point(17, 23);
    println!("left: {left}, right: {right}");
    // Also useful for making units.
    struct Newton(f64);
    impl std::fmt::Display for Newton {
        fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
            write!(f, "{} Newton", self.0)
        }
    }
    println!("An apple is about {}.", Newton(1.0));

    #[derive(Debug)]
    enum Direction {
        Left,
        Right,
    }
    #[derive(Debug)]
    enum PlayerMove {
        Pass,
        Run(Direction), // A one-tuple.
        Teleport { x: u32, y: u32 },
    }
    let m = PlayerMove::Run(Direction::Left);
    println!("On this turn: {m:?}");
    let m = PlayerMove::Teleport { x: 1, y: 2 };
    println!("On this turn: {m:?}");

    let moves = [
        PlayerMove::Pass,
        PlayerMove::Run(Direction::Right),
        PlayerMove::Teleport { x: 1, y: 2 },
    ];
    for mov in moves {
        match mov {
            PlayerMove::Pass => println!("Player passed"),
            PlayerMove::Run(dir) => println!("Running to the {dir:?}"),
            PlayerMove::Teleport { x, y } => println!("Teleporting to {x}, {y}"),
        }
    }

    // Contstants are inlined.
    #[allow(unused)]
    const A_CONST_NUM: i32 = 1;

    // Static variables are not moving ???

    // Type aliases
    use std::cell::RefCell;
    use std::sync::{Arc, RwLock};
    #[allow(unused)]
    type Inventory = RwLock<Vec<Arc<RefCell<i32>>>>;
}

// --------------------------------------------------------------------------------
// Exercise: Elevator Events.

fn exer_elevator_events() {
    #![allow(unused)]
    #[derive(Debug)]
    /// An event in the elevator system that the controller must react to.
    enum Event {
        ElevatorButton { floor: Floor, dir: Direction },
        CarButton { floor: Floor },
        Car { floor: Floor },
        CarDoor(DoorStatus),
    }

    /// A direction of travel.
    #[derive(Debug)]
    enum Direction {
        Up,
        Down,
    }

    #[derive(Debug)]
    enum DoorStatus {
        Open,
        Close,
    }

    #[derive(Debug)]
    struct Floor(i32);
    impl From<i32> for Floor {
        fn from(from: i32) -> Self {
            Floor(from)
        }
    }

    /// The car has arrived on the given floor.
    fn car_arrived(floor: i32) -> Event {
        Event::Car {
            floor: floor.into(),
        }
    }

    /// The car doors have opened.
    fn car_door_opened() -> Event {
        Event::CarDoor(DoorStatus::Open)
    }

    /// The car doors have closed.
    fn car_door_closed() -> Event {
        Event::CarDoor(DoorStatus::Close)
    }

    /// A directional button was pressed in an elevator lobby on the given floor.
    fn lobby_call_button_pressed(floor: i32, dir: Direction) -> Event {
        Event::ElevatorButton {
            floor: floor.into(),
            dir,
        }
    }

    /// A floor button was pressed in the elevator car.
    fn car_floor_button_pressed(floor: i32) -> Event {
        Event::CarButton {
            floor: floor.into(),
        }
    }

    println!(
        "A ground floor passenger has pressed the up button: {:?}",
        lobby_call_button_pressed(0, Direction::Up)
    );
    println!(
        "The car has arrived on the ground floor: {:?}",
        car_arrived(0)
    );
    println!("The car door opened: {:?}", car_door_opened());
    println!(
        "A passenger has pressed the 3rd floor button: {:?}",
        car_floor_button_pressed(3)
    );
    println!("The car door closed: {:?}", car_door_closed());
    println!("The car has arrived on the 3rd floor: {:?}", car_arrived(3));
}

// --------------------------------------------------------------------------------

fn main() {
    // Day 1:
    hello_world();
    variables();
    values();
    loops();
    macros();
    arrays();
    references();
    slices();
    strings();
    defining_types();
    exer_elevator_events();
}
