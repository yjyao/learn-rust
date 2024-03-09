#[macro_use]
extern crate assert_float_eq;

fn hello_world() {
    println!("Hello, world!");
    // `println!` is a macro.
}

// --------------------------------------------------------------------------------

fn variables() {
    let x: i32 = 10;
    assert_eq!(x, 10);
    // x = 20;  // ERROR: variables are by default immutable.

    let mut x: i32 = 10; // Can shadow variables.
    assert_eq!(x, 10);
    x = 20; // This is ok because `x` is mutable now.
    assert_eq!(x, 20);
    // x = "hey";  // ERROR: type mismatch.
    let x: String = String::from("hey"); // Redeclare `x` to be a string is ok.
    assert_eq!(x, "hey");

    // Formatting variables.
    // `format!` returns a formatted string.
    // `println!` prints it out to stdout.
    let x: String = String::from("hey");
    assert_eq!(format!("x: {x}"), "x: hey");
    // println!("x: {x}");  // This prints "x: hey" to stdout.
    // Format option `:?` gives debug info.
    assert_eq!(format!("x: {:?}", x), "x: \"hey\"");
    // Format option `:#?` gives pretty-printed debug info
    // that, for example, includes line breaks for large arrays.
    assert_eq!(format!("x: {:#?}", x), "x: \"hey\"");
    // Alternative styles:
    assert_eq!(format!("x: {}", x), "x: hey");
    assert_eq!(format!("x: {x:?}"), "x: \"hey\"");

    // `struct`s can support the debug representation with '#[derive(Debug)]'.
}

// --------------------------------------------------------------------------------

fn values() {
    // Signed and unsigned integers: `i32`, `u64`, etc.: `1_000`, `123_i64`
    // Use `u32` or `u64` for list indices.
    // Floating numbers: `f32` and `f64`: `1.2e20`, `2_f32`

    // Sizes are usually inferred for integers and floating numbers.

    // `char` is just `i32`. Strings are not a collection of `char`s.

    // `bool` values are `true` and `false`. They are not aliases to `1` and `0`.

    fn takes_u32(x: u32) -> String {
        return format!("u32: {x}");
    }

    fn takes_i8(x: i8) -> String {
        return format!("i8: {x}");
    }

    let mut _x = 10;
    assert_eq!(takes_i8(_x), "i8: 10"); // Compiler infers `x` as `i8`.
    _x = 20;
    // _x = 1024;  // ERROR: 1024 is out of range of `i8`.
    // takes_u32(_x);  // ERROR: Type mismatch.
    assert_eq!(takes_u32(_x as u32), "u32: 20");
    // A couple of type casting operations exist.
    // See https://stackoverflow.com/a/28280042.
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
    // This is more idiomatic than using return whereever possible.
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
    // For loops.
    let mut x = 0;
    for i in [2, 3, 4] {
        x += i;
    }
    assert_eq!(x, 2 + 3 + 4);

    x = 0;
    for i in 2..5 {
        x += i;
    }
    assert_eq!(x, 2 + 3 + 4);

    x = 0;
    for i in 2..=4 {
        x += i;
    }
    assert_eq!(x, 2 + 3 + 4);

    // While loops.
    let mut x = 0;
    let mut i = 2;
    while i < 5 {
        x += i;
        i += 1;
    }
    assert_eq!(x, 2 + 3 + 4);

    // `loop`s:
    // -   similar to `while true`
    // -   evaluates to a value (`for` and `while` don't).
    let mut i = 0;
    let mut x = 0;
    let y = loop {
        i += 1;
        if i > 5 {
            // i = 6
            break i; // Entire `loop` evaluates to `i` (6).
        }
        if i % 2 == 0 {
            continue;
        }
        x += i; // Sum of **odd** numbers.
    };
    assert_eq!(x, 1 + 3 + 5);
    assert_eq!(y, 6);

    // Labeled loops for easy `break` management:
    let mut x = 0;
    'outer: for _i in 1..10 {
        for j in 2..8 {
            x += j;
            break 'outer;
        }
    }
    assert_eq!(x, 2); // Both loops exited after the first `x += j` execution.
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
    assert_eq!(5 + dbg!(x), 5 + 3);
    // ^ This also prints a debug info of `x` to stderr.
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
    let mut a: [i8; 5] = [42; 5];
    a[3] = 0;
    assert_eq!(a, [42, 42, 42, 0, 42]);
    // Use the debug formatter `:?` to print arrays.
    assert_eq!(format!("{a:?}"), "[42, 42, 42, 0, 42]");

    // Tuples are anonymous structs.
    let t = (7, true);
    assert_eq!(t.0, 7);
    assert_eq!(t.1, true);
    // Use the debug formatter `:?` to print tuples.
    assert_eq!(format!("{t:?}"), "(7, true)");

    // Tuple unpacking.
    let pair = (3, 5);
    let (left, right) = pair;
    assert_eq!(left, 3);
    assert_eq!(right, 5);

    let tuple = (3, 5, 7, 8);
    let (first, second, ..) = tuple;
    assert_eq!(first, 3);
    assert_eq!(second, 5);

    let arr = [3, 5, 7, 8];
    let [first, rest @ ..] = arr;
    assert_eq!(first, 3);
    assert_eq!(rest, [5, 7, 8]);
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
    assert_eq!(*r, a);
    assert_eq!(*r, 'a');
    // r = &b;  // ERROR: `r` is immutable.
    let mut r: &char = &a;
    r = &b;
    assert_eq!(*r, b);
    assert_eq!(*r, 'b');
    // *r = 'x';  // ERROR: `r` is not a mutable/exclusive reference.
    let r = &mut b;
    *r = 'x';
    assert_eq!(*r, 'x');
    assert_eq!(b, 'x');
    // NOTE mutable references are exclusive.
    // So `b` and `*r` cannot both be able to mutate `b`.
    // The following code will produce an error:
    // ```
    // b = 'X';  // Ok. Implying that `r` is dead.
    // dbg!(*r);  // ERROR: `r` is still alive and also able to mutate `b`.
    // ```
}

// --------------------------------------------------------------------------------

fn slices() {
    let mut a = [10, 20, 30, 40, 50, 60];
    let s: &mut [i32] = &mut a[2..4];
    assert_eq!(s, [30, 40]);
    s[0] = 888;
    assert_eq!(s, [888, 40]);
    assert_eq!(a, [10, 20, 888, 40, 50, 60]);

    // The length of a slice can be a variable:
    // recall how array lengths are fixed at compile time
    // so it cannot be a variable.
    let end = 4;
    let s = &mut a[..end];
    assert_eq!(s.len(), 4);
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

    let mut reversed = String::new();
    for chara in s.chars() {
        reversed.insert(0, chara);
    }
    assert_eq!(reversed, "界世 olleh");

    // Get the character after '世':
    let start = s
        .find("世") //
        .unwrap(); // Ignore errors if any.
    let s1 = &s[start..];
    assert_eq!(s1.chars().skip(1).next().unwrap(), '界');
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
    let peter = Person { name: String::from("Peter"), age: 27 };
    assert_eq!(
        format!("{} is {} years old", peter.name, peter.age),
        "Peter is 27 years old"
    );

    // Initializing using existing data.
    let jackie = Person { name: String::from("Jackie"), ..peter };
    assert_eq!(
        format!("{} is also {} years old", jackie.name, jackie.age),
        "Jackie is also 27 years old"
    );

    // A "tuple struct".
    struct Point(i32, i32);
    let Point(left, right) = Point(17, 23);
    assert_eq!(left, 17);
    assert_eq!(right, 23);
    // Also useful for making units.
    struct Newton(f64);
    impl std::fmt::Display for Newton {
        fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
            write!(f, "{} Newton", self.0)
        }
    }
    assert_eq!(
        format!("An apple is about {}", Newton(1.0)),
        "An apple is about 1 Newton"
    );

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
    assert_eq!(format!("{m:?}"), "Run(Left)");
    let m = PlayerMove::Teleport { x: 1, y: 2 };
    assert_eq!(format!("{m:?}"), "Teleport { x: 1, y: 2 }");

    let moves = [
        PlayerMove::Pass,
        PlayerMove::Teleport { x: 1, y: 2 },
        PlayerMove::Run(Direction::Right),
    ];
    let mut move_history = String::new();
    for mov in moves {
        match mov {
            PlayerMove::Pass => move_history.push_str("Player passed\n"),
            PlayerMove::Run(dir) => move_history.push_str(&format!("Running to the {dir:?}\n")),
            PlayerMove::Teleport { x, y } => {
                move_history.push_str(&format!("Teleporting to ({x}, {y})\n"))
            }
        }
    }
    assert_eq!(
        move_history,
        "Player passed\n\
         Teleporting to (1, 2)\n\
         Running to the Right\n"
    );

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

#[test]
fn test_elevator_events() {
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
        Event::Car { floor: floor.into() }
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
        Event::ElevatorButton { floor: floor.into(), dir }
    }

    /// A floor button was pressed in the elevator car.
    fn car_floor_button_pressed(floor: i32) -> Event {
        Event::CarButton { floor: floor.into() }
    }

    // Tests.

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

fn pattern_matching() {
    let user_input = 'y';
    let resp = String::from(match user_input {
        // Using simple values.
        'q' => "Quitting",
        'y' | 'Y' => "Confirm",
        // Using a range.
        '0'..='9' => "Number input",
        // Using a variable binding and a "match guard".
        key if key.is_lowercase() => "Input is lowercase",
        // Using a wild card.
        _ => "Default",
    });
    assert_eq!(resp, "Confirm"); // Instead of "Input is lowercase".

    // NOTE: Must exhaust possible patterns to compile.
    // This won't compile:
    // ```
    // match 'x' {
    //     'a'..='c' => (),
    // }
    // ```

    // Unpacking in match patterns.
    struct Foo {
        x: u32,
        y: (u32, u32),
    }
    assert_eq!(
        match (Foo { x: 1, y: (2, 3) }) {
            Foo { x, y: (2, b) } => format!("x = {x}, y = (2, {b})"),
            Foo { y, .. } => format!("y = {y:?}, other fields were ignored."),
        },
        "x = 1, y = (2, 3)"
    );

    #[derive(Debug)]
    struct Person {
        name: String,
    }
    #[allow(unused)]
    enum FamilyMember {
        Father(Person),
        Mother(Person),
        Me(Person),
    }
    assert_eq!(
        match FamilyMember::Mother(Person { name: String::from("Alex") }) {
            FamilyMember::Father(father) => format!("father is {father:?}"),
            FamilyMember::Mother(Person { name, .. }) => format!("{name} is the mother"),
            _ => String::from("other case"),
        },
        "Alex is the mother"
    );

    // Shadowing
    #[allow(unused)]
    let a = 2;
    assert_eq!(
        match 3 {
            // This creates a new temporary variable `a`
            // that matches any `i32`.
            // This is NOT the `a` we declared above.
            a => format!("3 matches a, a = {a}"),
        },
        "3 matches a, a = 3"
    );
    const A: i32 = 2;
    assert_eq!(
        match 3 {
            // Constants are captured.
            // (probably because constants are inlined everywhere?)
            A => format!("3 does not match A which is 2"),
            _ => format!("3 goes to default"),
        },
        "3 goes to default"
    );
}

// --------------------------------------------------------------------------------

fn let_control_flow() {
    // Common usage: handling `Result` (`Ok`/`Err`) or `Option` (`Some`/`None`) values.

    // if-let
    const DEFAULT_DURATION: std::time::Duration = std::time::Duration::from_millis(500);
    fn get_duration(secs: f32) -> std::time::Duration {
        if let Ok(dur) = std::time::Duration::try_from_secs_f32(secs) {
            dur
        } else {
            DEFAULT_DURATION
        }
    }
    // Valid `secs` value, using 0.8 secs.
    assert_eq!(get_duration(0.8).as_millis(), 800);
    // Invalid `secs` value, using default duration.
    assert_eq!(get_duration(-10.0), DEFAULT_DURATION);

    // while-let
    let mut name = String::from("Hello World");
    let mut l_count = 0;
    while let Some(c) = name.pop() {
        if c == 'l' {
            l_count += 1;
        }
    }
    assert_eq!(l_count, 3);

    // direct let-else
    fn as_hex(maybe_string: Option<String>) -> Result<u32, String> {
        let Some(s) = maybe_string else {
            return Err(String::from("got None"));
        };
        let Some(first_char) = s.chars().next() else {
            return Err(String::from("got empty string"));
        };
        let Some(digit) = first_char.to_digit(16) else {
            return Err(String::from("not a hex digit"));
        };
        return Ok(digit);
    }
    assert_eq!(as_hex(None), Err(String::from("got None")));
    assert_eq!(as_hex(Some(String::from("foo"))), Ok(15));
}

// --------------------------------------------------------------------------------
// Exercise: Expr Eval.

/// An operation to perform on two subexpressions.
#[derive(Debug)]
#[allow(unused)]
enum Operation {
    Add,
    Sub,
    Mul,
    Div,
}

/// An expression, in tree form.
#[derive(Debug)]
#[allow(unused)]
enum Expression {
    /// A binary operation on two subexpressions.
    Op {
        op: Operation,
        left: Box<Expression>,
        right: Box<Expression>,
    },

    /// A literal value.
    Value(i64),
}

#[allow(unused)]
fn eval(e: Expression) -> Result<i64, String> {
    let (op, left, right) = match e {
        Expression::Value(v) => return Ok(v),
        Expression::Op { op, left, right } => (op, left, right),
    };
    let left = match eval(*left) {
        Ok(v) => v,
        err @ Err(_) => return err,
    };
    let right = match eval(*right) {
        Ok(v) => v,
        err @ Err(_) => return err,
    };
    Ok(match op {
        Operation::Add => left + right,
        Operation::Sub => left - right,
        Operation::Mul => left * right,
        Operation::Div => {
            if right != 0 {
                left / right
            } else {
                return Err(String::from("division by zero"));
            }
        }
    })
}

#[test]
fn test_value() {
    assert_eq!(eval(Expression::Value(19)), Ok(19));
}

#[test]
fn test_sum() {
    assert_eq!(
        eval(Expression::Op {
            op: Operation::Add,
            left: Box::new(Expression::Value(10)),
            right: Box::new(Expression::Value(20)),
        }),
        Ok(30)
    );
}

#[test]
fn test_recursion() {
    let term1 = Expression::Op {
        op: Operation::Mul,
        left: Box::new(Expression::Value(10)),
        right: Box::new(Expression::Value(9)),
    };
    let term2 = Expression::Op {
        op: Operation::Mul,
        left: Box::new(Expression::Op {
            op: Operation::Sub,
            left: Box::new(Expression::Value(3)),
            right: Box::new(Expression::Value(4)),
        }),
        right: Box::new(Expression::Value(5)),
    };
    assert_eq!(
        eval(Expression::Op {
            op: Operation::Add,
            left: Box::new(term1),
            right: Box::new(term2),
        }),
        Ok(85)
    );
}

#[test]
fn test_error() {
    assert_eq!(
        eval(Expression::Op {
            op: Operation::Div,
            left: Box::new(Expression::Value(99)),
            right: Box::new(Expression::Value(0)),
        }),
        Err(String::from("division by zero"))
    );
}

// --------------------------------------------------------------------------------

fn methods() {
    #[derive(Debug)]
    struct Race {
        name: String,
        laps: Vec<i32>,
    }
    impl Race {
        // Static method because of lack of the receiver `self`.
        fn new(name: &str) -> Self {
            Self { name: String::from(name), laps: Vec::new() }
        }
        // The receiver `self` is short for `self: Self` or `self: Race`.
        // `Self` is an automatic type alias to `Race`.
        // Exclusive borrowed read-write access.
        fn add_lap(&mut self, lap: i32) {
            self.laps.push(lap);
        }
        // Shared borrowed read-only access.
        fn print_laps(&self) -> String {
            let mut out = String::new();
            out.push_str(&format!(
                "Recorded {} laps for {}:\n",
                self.laps.len(),
                self.name
            ));
            for (i, lap) in self.laps.iter().enumerate() {
                out.push_str(&format!("Lap {i}: {lap} sec\n"));
            }
            out
        }
        // Exclusive ownership of self.
        // Kinda like a destrctor,
        // unless this method then transfers the ownership away.
        // `mut self` works similarly except it allows modification to `self`.
        fn finish(self) -> String {
            let total: i32 = self.laps.iter().sum();
            format!("Race {} is finished, total lap time: {}", self.name, total)
        }
    }

    let mut race = Race::new("Monaco Grand Prix");
    race.add_lap(70);
    assert_eq!(
        race.print_laps(),
        "Recorded 1 laps for Monaco Grand Prix:\n\
         Lap 0: 70 sec\n"
    );
    race.add_lap(68);
    assert_eq!(
        race.print_laps(),
        "Recorded 2 laps for Monaco Grand Prix:\n\
         Lap 0: 70 sec\n\
         Lap 1: 68 sec\n"
    );
    assert_eq!(
        race.finish(),
        "Race Monaco Grand Prix is finished, total lap time: 138"
    );
    // race.add_lap(42);  // ERROR: `Race::finish` takes the ownership away.
}

// --------------------------------------------------------------------------------

fn traits() {
    // Traits are like interfaces.
    trait Pet {
        /// Return a sentence from this pet.
        fn talk(&self) -> String;

        /// Return a string to the terminal greeting this pet.
        fn greet(&self) -> String {
            format!("Oh you're a cutie! What's your name? {}", self.talk())
        }
    }
    struct Dog {
        name: String,
    }
    // `impl` block is required to register `Dog` as a `Pet`.
    impl Pet for Dog {
        fn talk(&self) -> String {
            format!("Woof, my name is {}!", self.name)
        }
    }
    let fido = Dog { name: String::from("Fido") };
    assert_eq!(
        fido.greet(),
        "Oh you're a cutie! What's your name? Woof, my name is Fido!"
    );

    // We can use associated types
    // to allow the implementer to choose the type of the output,
    // instead of the caller.
    trait Multiply {
        type Output; // This is the "associated type", or "output type".
        fn multiply(&self, other: &Self) -> Self::Output;
    }

    #[derive(Debug)]
    struct Meters(i32);
    #[derive(Debug)]
    struct MetersSquared(i32);

    impl Multiply for Meters {
        type Output = MetersSquared;
        fn multiply(&self, other: &Self) -> Self::Output {
            MetersSquared(self.0 * other.0)
        }
    }

    assert_eq!(
        format!("{:?}", Meters(10).multiply(&Meters(20))),
        "MetersSquared(200)"
    );

    //
    #[derive(Debug, Clone, Default)]
    #[allow(unused)]
    struct Player {
        name: String,
        strength: u8,
        hit_points: u8,
    }
    let p1 = Player::default(); // Provided by the `Default` trait.
    let mut p2 = p1.clone(); // Provided by the `Clone` trait.
    p2.name = String::from("EldurScrollz");
    // `Debug` trait adds support for printing with `{:?}`.
    assert_eq!(
        format!("{:?} vs {:?}", p1, p2),
        r#"Player { name: "", strength: 0, hit_points: 0 } vs Player { name: "EldurScrollz", strength: 0, hit_points: 0 }"#
    );
}

// --------------------------------------------------------------------------------
// Exercise: Generic Logger

pub trait Logger {
    /// Log a message at the given verbosity level.
    fn log(&mut self, verbosity: u8, message: impl std::fmt::Display);
}

#[derive(Default)]
struct StringLogger {
    buffer: String,
}

impl Logger for StringLogger {
    fn log(&mut self, verbosity: u8, message: impl std::fmt::Display) {
        self.buffer
            .push_str(&format!("verbosity={verbosity}: {message}\n"));
    }
}

/// Only log messages up to the given verbosity level.
struct VerbosityFilter<L: Logger> {
    max_verbosity: u8,
    inner: L,
}

impl<L: Logger> Logger for VerbosityFilter<L> {
    fn log(&mut self, verbosity: u8, message: impl std::fmt::Display) {
        if verbosity < self.max_verbosity {
            self.inner.log(verbosity, message);
        }
    }
}

#[test]
fn test_verbosity_filter() {
    fn do_things(logger: &mut impl Logger) {
        logger.log(5, "FYI");
        logger.log(2, "Uhoh");
    }

    let mut logger = VerbosityFilter { max_verbosity: 3, inner: StringLogger::default() };
    do_things(&mut logger);
    assert_eq!(logger.inner.buffer, String::from("verbosity=2: Uhoh\n"));
}

// --------------------------------------------------------------------------------

fn generics() {
    // Generic functions.
    fn pick<T>(n: i32, even: T, odd: T) -> T {
        if n % 2 == 0 {
            even
        } else {
            odd
            // even + old  // ERROR: We don't know if `T` supports this.
        }
    }
    assert_eq!(pick(97, 222, 333), 333);
    assert_eq!(pick(28, ("dog", 1), ("cat", 2)), ("dog", 1));
    // ^ These are converted to non-generic code at compile time,
    // so running generic function are as fast as running regular functions.

    #[derive(Debug)]
    struct Point<T> {
        x: T,
        y: T,
    }
    impl<T> Point<T> {
        fn coords(&self) -> (&T, &T) {
            (&self.x, &self.y)
        }
    }
    assert_eq!(format!("{:?}", Point { x: 5, y: 10 }.coords()), "(5, 10)");
    assert_eq!(
        format!("{:?}", Point { x: "Hello", y: "World" }.coords()),
        "(\"Hello\", \"World\")"
    );

    // Generic type for traits.
    {
        #[allow(unused)]
        fn duplicate<T: Clone>(a: T) -> (T, T) {
            (a.clone(), a.clone())
        }
    }
    // Multiple traits.
    {
        #[allow(unused)]
        fn duplicate<T: Clone + std::fmt::Debug>(a: T) -> (T, String) {
            (a.clone(), format!("{a:?}"))
        }
    }
    // Alternatively specify trait templates with a `where` clause.
    {
        #[allow(unused)]
        fn duplicate<T>(a: T) -> (T, T)
        where
            T: Clone,
            // `where` clause also lets you add some constraints,
            // such as `Option<T>: MaybePet`.
        {
            (a.clone(), a.clone())
        }
    }
    // Alternatively specify trait templates with `impl Trait`.
    {
        #[allow(unused)]
        fn add_10(x: impl Into<i32>) -> i32 {
            x.into() + 10
        }
    }
    // Same as:
    {
        #[allow(unused)]
        fn add_10<T: Into<i32>>(x: T) -> i32 {
            x.into() + 10
        }
    }
    // `impl Trait` can be the return type.
    // This allows hiding the real return type.
    #[allow(unused)]
    fn pair_of(x: u32) -> impl std::fmt::Debug {
        (x + 1, x - 1)
    }
}

// --------------------------------------------------------------------------------
// Exercise: Generic `min`

trait LessThan {
    /// Return `true` if `self` is less than `other`.
    fn less_than(&self, other: &Self) -> bool;
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
struct Citation {
    author: &'static str,
    year: u32,
}

impl LessThan for Citation {
    fn less_than(&self, other: &Self) -> bool {
        if self.author < other.author {
            true
        } else if self.author > other.author {
            false
        } else {
            self.year < other.year
        }
    }
}

#[allow(unused)]
fn min<T: LessThan + Clone>(a: T, b: T) -> T {
    if a.less_than(&b) {
        a
    } else {
        b
    }
}

#[test]
fn test_min() {
    let cit1 = Citation { author: "Shapiro", year: 2011 };
    let cit2 = Citation { author: "Baumann", year: 2010 };
    let cit3 = Citation { author: "Baumann", year: 2019 };
    assert_eq!(min(cit1, cit2), cit2);
    assert_eq!(min(cit2, cit3), cit2);
    assert_eq!(min(cit1, cit3), cit3);
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
    pattern_matching();
    let_control_flow();
    methods();
    traits();
    generics();
}
