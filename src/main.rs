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
    let start = s.find("世").unwrap(); // `unwrap` might panic
                                       // but let's ignore that for now.
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

    // Initializing with existing data
    // using the "struct update syntax" (`..<var>`).
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
            right: Box::new(term2)
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

fn std_types() {
    // Layers:
    //
    // -   `core`: basic types with no dependencies.
    // -   `alloc`: types that depend on allocators or OS (like `Vec`).
    // -   `std`: standard utils.

    // Create doc strings in the code:
    //
    // - Use triple-slash comments `///` before function signatures.
    // - Use `//!` for module-level doc strings.
    // - Use `/*! .. */` for inner items.
    //
    // The `rustdoc` tool pulls these doc strings
    // to create a documentation on https://docs.rs.
    // Write these doc strings in Markdown.
    //

    // `Option`
    let maybe_n: Option<i32> = Some(10);
    assert_eq!(maybe_n.unwrap(), 10);
    #[allow(unused)]
    let maybe_n: Option<i32> = None;
    // maybe_n.unwrap();  // ERROR: Will panic.
    // maybe_n.expect("n is absent");  // ERROR: Similar to `unwrap`
    //                                 // but prints "n is absent" as the error.
    let maybe_n = Some(10);
    assert_eq!(maybe_n.expect("n is absent"), 10); // Same as `unwrap`.

    // Handy for prototyping.
    // Usually cleans up all the `unwrap`/`expect` on production code
    // and handle `None` better.

    let name = "Löwe 老虎 Léopard Gepardi";
    let mut position: Option<usize> = name.find('é');
    assert_eq!(format!("{position:?}"), "Some(14)");
    position = name.find('Z');
    assert_eq!(format!("{position:?}"), "None");

    // `Result`
    // Standard type to implement error handling.
    use std::fs::File;
    let file: Result<File, std::io::Error> = File::open("imaginary.file.txt");
    // Use `match` to unpack the `Result`:
    match file {
        Ok(_) => assert!(false),
        Err(_) => assert!(true),
    }
    // Alternatively, use `let-else` to unpack the `Result`:
    if let Ok(file) = File::open("imaginary.file.txt") {
        eprintln!("{file:?}");
        assert!(false);
    } else {
        assert!(true);
    }
    // If we know an error should never happen, we can `unwrap` directly:
    let guaranteed_value: Result<i32, String> = Ok(31);
    assert_eq!(guaranteed_value.unwrap(), 31);

    // `String`
    let mut s1 = String::new();
    assert_eq!(s1, "");
    assert_eq!(s1.len(), 0);
    s1.push_str("abc");
    assert_eq!(s1.len(), 3);
    s1 = String::from("你好");
    assert_eq!(s1.len(), 6); // `len` is the count of *bytes*,
                             // not visual characters.
    assert_eq!(s1.chars().count(), 2); // `chars` collects the characters.
                                       // But your concept of characters
                                       // can still differ from `chars`.
                                       // println!(s1[1..]);  // ERROR: "byte index 1 is not a char boundary."
    assert_eq!(s1.chars().nth(1).unwrap(), '好');

    s1 = String::with_capacity(2);
    assert_eq!(s1.capacity(), 2);
    s1.push_str("abc");
    assert!(s1.capacity() > 2); // Capacity grows as needed.

    s1 = String::from("world");
    let mut s2 = String::from("hello ");
    s2.push_str(&s1); // `s1` needs dereferencing to be casted to `&str`.
                      // `String` does this by
                      // implementing the `Deref<Target = str>` trait.
                      // This also lets `String` call any methods in `&str`.
    assert_eq!(s2, "hello world");

    // Implement `ToString` (don't) or `Display` traits for a struct
    // so it can be converted to a string.

    // `Vec`
    let mut v1: Vec<i32> = Vec::new();
    assert_eq!(v1.len(), 0);
    v1.push(42);
    assert_eq!(v1.len(), 1);

    let mut v2 = Vec::new(); // Rust infers `i32` on the first push.
                             // We don't have to specify.
    v2.extend(v1.iter());
    v2.push(31);
    assert_eq!(v2, [42, 31]);
    assert_eq!(v2.pop().unwrap(), 31);
    assert_eq!(v2, [42]);
    // v1.push("hey");  // ERROR: Rust already infers that `v2` is a `Vec<i32>`,
    //                  // so this is a type mismatch.

    // Canonical macro to initialize a vector with elements.
    let mut v3 = vec![0, 0, 1, 2, 3, 4, 2];

    // Retain only the even elements.
    v3.retain(|x| x % 2 == 0);
    assert_eq!(v3, [0, 0, 2, 4, 2]);

    // Remove consecutive duplicates.
    v3.dedup();
    assert_eq!(v3, [0, 2, 4, 2]);

    // `Vec` implements `Deref<Target = [T]`
    // so you can call slice methods on a `Vec`.
    // Like the index-based item getter `[]`.
    let v4 = vec![2, 3, 4];
    assert_eq!(v4[1], 3);
    // eprintln!("{}", v4[10]);  // ERROR: out of bounds.
    assert_eq!(v4.get(1).unwrap(), &3);
    assert_eq!(v4.get(10), None);

    // `HashMap`
    use std::collections::HashMap;
    let mut page_counts = HashMap::new();
    page_counts.insert("Adventures of Huckleberry Finn".to_string(), 207);
    page_counts.insert("Grimms' Fairy Tales".to_string(), 751);
    page_counts.insert("Pride and Prejudice".to_string(), 303);
    // ^ Noticed the `to_string`? NOTE Do NOT use `&str` as key!

    assert_eq!(page_counts.len(), 3);
    assert_eq!(page_counts.contains_key("Les Misérables"), false);

    match page_counts.get("西游记") {
        Some(_) => assert!(false),
        None => assert!(true),
    }

    let page_count: &mut i32 = page_counts.entry("三国演义".to_string()).or_insert(0);
    *page_count += 1;
    assert_eq!(page_counts.get("三国演义").unwrap(), &1);
    let count = page_counts.get("1984").unwrap_or(&336);
    assert_eq!(count, &336);
    assert_eq!(page_counts.contains_key("1984"), false);

    let prices = HashMap::from([
        ("Apple".to_string(), 8), //
        ("Banana".to_string(), 5),
    ]);
    let mut fruits: Vec<_> = prices.keys().collect();
    fruits.sort(); // `keys()` returns in arbitrary order.
    assert_eq!(fruits, ["Apple", "Banana"]);
}

// --------------------------------------------------------------------------------
// Exercise: Counter

#[test]
fn test_counter() {
    use std::collections::HashMap;
    use std::hash::Hash;

    /// Counter counts the number of times each value of type T has been seen.
    struct Counter<T: Eq + Hash> {
        counts: HashMap<T, u64>,
    }

    impl<T: Eq + Hash> Counter<T> {
        /// Create a new Counter.
        fn new() -> Self {
            Counter { counts: HashMap::new() }
        }

        /// Count an occurrence of the given value.
        fn count(&mut self, value: T) {
            *self.counts.entry(value).or_insert(0) += 1;
        }

        /// Return the number of times the given value has been seen.
        fn times_seen(&self, value: T) -> u64 {
            self.counts.get(&value).copied().unwrap_or_default()
        }
    }

    let mut ctr = Counter::new();
    ctr.count(13);
    ctr.count(14);
    ctr.count(16);
    ctr.count(14);
    ctr.count(14);
    ctr.count(11);

    assert_eq!(ctr.times_seen(10), 0);
    assert_eq!(ctr.times_seen(11), 1);
    assert_eq!(ctr.times_seen(12), 0);
    assert_eq!(ctr.times_seen(13), 1);
    assert_eq!(ctr.times_seen(14), 3);
    assert_eq!(ctr.times_seen(15), 0);
    assert_eq!(ctr.times_seen(16), 1);
    assert_eq!(ctr.times_seen(17), 0);

    let mut strctr = Counter::new();
    strctr.count("apple");
    strctr.count("orange");
    strctr.count("apple");
    assert_eq!(strctr.times_seen("apple"), 2);
    assert_eq!(strctr.times_seen("orange"), 1);
    assert_eq!(strctr.times_seen("banana"), 0);

    // Make sure `times_seen` does not count.
    assert_eq!(strctr.times_seen("apple"), 2);
    assert_eq!(strctr.times_seen("orange"), 1);
    assert_eq!(strctr.times_seen("banana"), 0);
}

// --------------------------------------------------------------------------------

fn overloading_comparisons() {
    // `PartialEq` and `Eq`
    struct Person {
        name: String,
        id: u32,
    }
    impl PartialEq for Person {
        fn eq(&self, other: &Self) -> bool {
            self.id == other.id
        }
    }
    let adam = Person { name: "Adam".to_string(), id: 12315 };
    let ben = Person { name: "Ben".to_string(), id: 10086 };
    assert!(adam == Person { name: adam.name.clone(), id: adam.id });
    assert!(adam != ben);
    // Equality only depends on the ID#:
    assert!(adam != Person { name: adam.name.clone(), id: 0 });
    assert!(adam == Person { name: ben.name.clone(), id: adam.id });
    // `Eq` implements the full equivalence relation.

    // `PartialOrd` and `Ord`
    use std::cmp::Ordering;
    #[derive(Eq, PartialEq)]
    struct Citation {
        author: String,
        year: u32,
    }
    // Sort by author first, then year.
    impl PartialOrd for Citation {
        fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
            match self.author.partial_cmp(&other.author) {
                Some(Ordering::Equal) => self.year.partial_cmp(&other.year),
                author_ord => author_ord,
            }
        }
    }
    // `Ord` implements total ordering.
    // Ordering can happen between different types. Equality cannot.

    // NOTE In practice,
    // it's common to just derive these traits
    // *without* implementing them.
}

// --------------------------------------------------------------------------------

fn overloading_operators() {
    // Overload operators by implementing `std::ops` traits.
    #[derive(PartialEq, Debug, Copy, Clone)]
    struct Point {
        x: i32,
        y: i32,
    }
    // We can additionally implement `Add` for `&Point`
    // to avoid unnecessary copies.
    impl std::ops::Add for Point {
        type Output = Self;
        fn add(self, other: Self) -> Self {
            Self { x: self.x + other.x, y: self.y + other.y }
        }
    }
    let p1 = Point { x: 10, y: 20 };
    let p2 = Point { x: 100, y: 200 };
    assert_eq!(p1 + p2, Point { x: 110, y: 220 });
    // `p1` and `p2` are still available thanks to `Copy` and `Clone` traits.
    // If you remove them, the following line will error out.
    assert_eq!(p1 + p2, Point { x: 110, y: 220 });

    // We can also overload for adding `Point`s to different types.
    // Let's implement for `&Point` this time around.
    impl std::ops::Add<&(i32, i32)> for &Point {
        type Output = Point;
        fn add(self, other: &(i32, i32)) -> Self::Output {
            Self::Output { x: self.x + other.0, y: self.y + other.1 }
        }
    }
    assert_eq!(&p1 + &(3, 2), Point { x: 13, y: 22 });
    // ^ `&p1` does not consume `p1`.
    // So even without deriving `Copy` and `Clone`,
    // we would still have access over `p1` after the operation.
}

// --------------------------------------------------------------------------------

fn casting() {
    // `From` and `Into`
    #[derive(PartialEq, Debug)]
    struct Point {
        x: i32,
        y: i32,
    }
    impl From<(i32, i32)> for Point {
        fn from(pt: (i32, i32)) -> Self {
            Self { x: pt.0, y: pt.1 }
        }
    }
    assert_eq!(Point::from((2, 3)), Point { x: 2, y: 3 });
    // `Into<Point> for (i32, i32)` is automatically implemented by `From`:
    assert_eq!(Point { x: 2, y: 3 }, (2, 3).into());
    // It's common to only implement the `From` trait,
    // and use `T: Into<SomeThing>` as templates.

    #[allow(unused)]
    {
        let s = String::from("hello");
        let addr = std::net::Ipv4Addr::from([127, 0, 0, 1]);
        let one = i16::from(true);
        let bigger = i32::from(123_i16);

        let s: String = "hello".into();
        let addr: std::net::Ipv4Addr = [127, 0, 0, 1].into();
        let one: i16 = true.into();
        let bigger: i32 = 123_i16.into();
    }

    // Casting with `as` is possible, but *dangerous*:
    // it is easy to use `as` incorrectly.
    let value: i64 = 1000;
    assert_eq!(1000, value as u16);
    assert_eq!(1000, value as i16);
    assert_eq!(232, value as u8);

    // Best practices:
    //
    // - Only use `as` to indicate unconditional truncation.
    // - For small -> big casts (no data loss), use `From`/`Into`.
    // - For big -> small casts (possible data loss), use `TryFrom`/`TryInto`.
}

// --------------------------------------------------------------------------------

fn read_write() {
    use std::io::{BufRead, BufReader, Read};

    fn count_lines<R: Read>(reader: R) -> usize {
        let buf_reader = BufReader::new(reader);
        buf_reader.lines().count()
    }

    let slice: &[u8] = b"foo\nbar\nbaz\n";
    assert_eq!(count_lines(slice), 3);

    let file = std::fs::File::open(std::env::current_exe().unwrap()).unwrap();
    eprintln!("lines in the compiled execucatble: {}", count_lines(file));

    use std::io::Write;

    fn log<W: Write>(writer: &mut W, msg: &str) -> std::io::Result<()> {
        writer.write_all(msg.as_bytes())?; // The `?` returns if error.
        writer.write_all("\n".as_bytes())
    }

    let mut buffer = Vec::new();
    if let Err(_) = log(&mut buffer, "Hello") {
        panic!();
    }
    if let Err(_) = log(&mut buffer, "World") {
        panic!();
    }
    assert_eq!(buffer.len(), "Hello\nWorld\n".chars().count());
}

// --------------------------------------------------------------------------------

fn impl_default() {
    #![allow(unused)]

    // The `Default` trait fills default values.

    // Can be derived.
    #[derive(Debug, Default)]
    struct Derived {
        x: u32,
        y: String,
        z: Implemented,
    }

    // Alternatively, you can implement `Default` directly.
    #[derive(Debug)]
    struct Implemented(String);
    impl Default for Implemented {
        fn default() -> Self {
            Self("John Smith".into())
        }
    }

    assert_eq!(
        format!("{:?}", Derived::default()),
        r#"Derived { x: 0, y: "", z: Implemented("John Smith") }"#
    );

    assert_eq!(
        format!(
            "{:?}",
            Derived { y: "Y is set!".into(), ..Derived::default() }
        ),
        r#"Derived { x: 0, y: "Y is set!", z: Implemented("John Smith") }"#
    );

    let none: Option<Derived> = None;
    assert_eq!(
        format!("{:?}", none.unwrap_or_default()),
        r#"Derived { x: 0, y: "", z: Implemented("John Smith") }"#
    );
}

// --------------------------------------------------------------------------------

fn closures() {
    // Closures are also called lambda expressions.

    // `FnOnce` includes both `Fn` and `FnMut`.
    // So this is really saying "any lambda".
    fn apply_then_double(func: impl FnOnce(i32) -> i32, input: i32) -> i32 {
        2 * func(input)
    }

    let add_3 = |x| x + 3; // This is an `Fn`.
                           // `Fn`s cannot consume or capture values.
                           // `add_3` captures no values at all.
    assert_eq!(apply_then_double(add_3, 10), 2 * (10 + 3));

    // An example that does capture values.
    let mut v = Vec::new();
    let mut accumulate = |x: i32| {
        v.push(x);
        v.iter().sum::<i32>()
    }; // This is an `FnMut`. It can mutate the captured value `v`.
    assert_eq!(apply_then_double(&mut accumulate, 4), 2 * (4));
    assert_eq!(apply_then_double(&mut accumulate, 6), 2 * (4 + 6));
    assert_eq!(apply_then_double(&mut accumulate, 2), 2 * (4 + 6 + 2));

    // This is an `FnOnce` because it consumes the captured value.
    let multiply_sum = |x| x * v.into_iter().sum::<i32>();
    assert_eq!(apply_then_double(multiply_sum, 5), 2 * 5 * (4 + 6 + 2));
    // let _ = apply_then_double(multiply_sum, 5);  // ERROR: `v` has been consumed.

    // Compiler infers `Copy` and/or `Clone`
    // depending on what the colsure captures.

    fn make_greeter(prefix: String) -> impl Fn(String) -> String {
        // By default, closures capture by reference.
        // Here, `prefix` will die after `make_greeter` returns,
        // breaking the returned greeter function.
        // With the `move` keyword the closure captures by value
        // (i.e., it copies `prefix`).
        return move |name| format!("{} {}", prefix, name);
    }

    let hi = make_greeter("Hi,".into());
    assert_eq!(hi("Greg".into()), "Hi, Greg");
}

// --------------------------------------------------------------------------------
// Exercise: ROT13

// fn main() {
//     let mut rot =
//         RotDecoder { input: "Gb trg gb gur bgure fvqr!".as_bytes(), rot: 13 };
//     let mut result = String::new();
//     rot.read_to_string(&mut result).unwrap();
//     println!("{}", result);
// }

#[cfg(test)]
mod test {
    use std::io::Read;

    struct RotDecoder<R: Read> {
        input: R,
        rot: u8,
    }

    // Implement the `Read` trait for `RotDecoder`.
    impl<R: Read + std::fmt::Debug> Read for RotDecoder<R> {
        /// Decode `self.input` into `buf`. Only rotate ASCII alphabetic characters.
        fn read(&mut self, buf: &mut [u8]) -> std::io::Result<usize> {
            let size = self.input.read(buf)?;
            for byte in &mut buf[..size] {
                if !byte.is_ascii_alphabetic() { continue }
                let base = if byte.is_ascii_uppercase() { 'A' } else { 'a' } as u8;
                *byte = base + (*byte - base + self.rot) % 26;
            }
            Ok(size)
        }
    }

    #[test]
    fn joke() {
        let mut rot = RotDecoder {
            input: "Gb trg gb gur bgure fvqr!".as_bytes(),
            rot: 13,
        };
        let mut result = String::new();
        rot.read_to_string(&mut result).unwrap();
        assert_eq!(&result, "To get to the other side!");
    }

    #[test]
    fn binary() {
        let input: Vec<u8> = (0..=255u8).collect();
        let mut rot = RotDecoder::<&[u8]> { input: input.as_ref(), rot: 13 };
        let mut buf = [0u8; 256];
        assert_eq!(rot.read(&mut buf).unwrap(), 256);
        for i in 0..=255 {
            if input[i] != buf[i] {
                assert!(input[i].is_ascii_alphabetic());
                assert!(buf[i].is_ascii_alphabetic());
            }
        }
    }
}

// --------------------------------------------------------------------------------

fn memory_mgt() {
    // Two ways of memory allocation:
    //
    // - **Stack**:
    //     - Continuous area of memory.
    //     - Stores fixed sizes for values.
    //     - Fast.
    //     - Great memory locality.
    //
    // - **Heap**:
    //     - Stores values of dynamic sizes.
    //     - Slightly slower.
    //     - No guarantee of memory locality.

    // `String` is a wraper over `Vec` --- they both have dynamic sizes.
    // So `String` puts
    // - fixed-sized metadata on the stack and
    // - the actual string on the heap.

    // Common languages fall into two categories:
    //
    // - Manual but full memory control.
    //     - Manual
    //     - Prone to mistakes
    // - Automatic and safe memory control.
    //     - Programmer has partial control.
    //     - Typically relies on garbage collectors that are slow.
    //
    // Rust provides full control and safety
    // at zero performance cost
    // via compile time enforcement of memory management.

    // Variable bindings have a scope.
    // Using a variable outside its scope is an error.
    {
        let i = 1;
        assert_eq!(i, 1);
    }  // `i` is dropped here and the value is freed.
    // assert_eq!(i, 1);  // ERROR: `i` is undefined.

    // Every value has precisely one owner at any time.
    // An assignment transfers ownership.
    let s1 = "Hello".to_string();
    let s2 = s1;
    assert_eq!(s2, "Hello");
    // assert_eq!(s1, "Hello");  // ERROR: `s1` no longer owns the value.

    // Passing a value to a function also transfers ownership.
    fn consume(_: String) { () }
    let name = "Alice".to_string();
    assert_eq!(name, "Alice");
    consume(name);
    // assert_eq!(name, "Alice");  // ERROR: Ownership transferred from `name`
    //                             // to the function parameter.
    let name = "Bob".to_string();
    consume(name.clone());  // Need to pass by copy explicitly.
    assert_eq!(name, "Bob");  // Ok.

    // In C++:
    // ```cc
    // std::string s1 = "Cpp";
    // std::string s2 = s1;
    // ```
    // C++ duplicates the heap data from `s1` to `s2`
    // so they are independent copies.
    //
    // C++ also has `std::move`:
    // ```cc
    // std::string s1 = "Cpp";
    // std::string s2 = std::move(s1);
    // ```
    // In this case,
    // `s1` is in an unspecified,
    // using `s1` is allowed but might cause problems.
    //
    // Back to Rust.

    // Implementing `Clone` trait enables a type to be copied.
    // It makes it easy to spot heap allocations in code.
    // In practice,
    // when prototyping
    // you would often "clone your way out" of problems
    // when the borrow checker complains,
    // and then later try to optimize them away.

    // Implementing `Copy` trait lets you copy implicitly.
    let x = 31;
    let y = x;
    assert_eq!(x, y);  // Ok. `y` is a copy.

    // NOTE "Copy" and "clone" are different:
    //
    // - Copying is bit-wise copy of memory regions.
    // - Copying has no custom logic.
    // - Copying does not work on types implementing the `Drop` trait.

    // Implement `Drop` trait to run code when they go out of scope.
    // To run the code before the end of the scope, call `drop(obj)`.
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
    // Day 2:
    pattern_matching();
    let_control_flow();
    methods();
    traits();
    generics();
    std_types();
    overloading_comparisons();
    overloading_operators();
    casting();
    read_write();
    impl_default();
    closures();
    // Day 3:
    memory_mgt();
}
