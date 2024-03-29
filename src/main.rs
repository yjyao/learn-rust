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

#[cfg(test)]
mod exercise_fibonacci {
    #![allow(unused)]

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

#[cfg(test)]
mod exercise_collatz_length {
    #![allow(unused)]

    // Determine the length of the collatz sequence beginning at `n`.
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

#[cfg(test)]
mod exercise_transpose {
    #![allow(unused)]

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

#[cfg(test)]
mod exercise_geometry {
    #![allow(unused)]

    // Calculate the magnitude of a vector by summing the squares of its coordinates
    // and taking the square root. Use the `sqrt()` method to calculate the square
    // root, like `v.sqrt()`.
    fn magnitude(vector: &[f64]) -> f64 {
        let mut res = 0.0;
        for n in vector {
            res += n * n;
        }
        res.sqrt()
    }

    // Normalize a vector by calculating its magnitude and dividing all of its
    // coordinates by that magnitude.
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

#[cfg(test)]
mod exercise_elevator_events {
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

    #[test]
    fn test_elevator_events() {
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

#[cfg(test)]
mod exercise_expression_evaluation {
    #![allow(unused)]

    /// An operation to perform on two subexpressions.
    #[derive(Debug)]
    enum Operation {
        Add,
        Sub,
        Mul,
        Div,
    }

    /// An expression, in tree form.
    #[derive(Debug)]
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

#[cfg(test)]
mod exercise_generic_logger {
    #![allow(unused)]

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

#[cfg(test)]
mod exercise_generic_min {
    #![allow(unused)]

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
    page_counts.insert(String::from("Adventures of Huckleberry Finn"), 207);
    page_counts.insert(String::from("Grimms' Fairy Tales"), 751);
    page_counts.insert(String::from("Pride and Prejudice"), 303);
    // ^ Noticed the `to_string`? NOTE Do NOT use `&str` as key!

    assert_eq!(page_counts.len(), 3);
    assert_eq!(page_counts.contains_key("Les Misérables"), false);

    match page_counts.get("西游记") {
        Some(_) => assert!(false),
        None => assert!(true),
    }

    let page_count: &mut i32 = page_counts.entry(String::from("三国演义")).or_insert(0);
    *page_count += 1;
    assert_eq!(page_counts.get("三国演义").unwrap(), &1);
    let count = page_counts.get("1984").unwrap_or(&336);
    assert_eq!(count, &336);
    assert_eq!(page_counts.contains_key("1984"), false);

    let prices = HashMap::from([
        (String::from("Apple"), 8), //
        (String::from("Banana"), 5),
    ]);
    let mut fruits: Vec<_> = prices.keys().collect();
    fruits.sort(); // `keys()` returns in arbitrary order.
    assert_eq!(fruits, ["Apple", "Banana"]);
}

// --------------------------------------------------------------------------------

#[cfg(test)]
mod exercise_counter {
    #![allow(unused)]

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

    #[test]
    fn test_counter() {
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
    let adam = Person { name: String::from("Adam"), id: 12315 };
    let ben = Person { name: String::from("Ben"), id: 10086 };
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

    // If you derive both `Copy` and `Clone`, DON'T implement `Clone`
    // because that would be confusing.
    // Also in this case `p1` (copy by default) is faster than `p1.clone()`
    // because `.clone()` is a function call
    // and is harder to optimize away for the compiler.
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
        panic!()
    }
    if let Err(_) = log(&mut buffer, "World") {
        panic!()
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

#[cfg(test)]
mod exercise_rot13 {
    #![allow(unused)]

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
                if !byte.is_ascii_alphabetic() {
                    continue;
                }
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
    //     - Limited volume.
    //     - Automatic, following function calls. The programmer does not need to manage.
    //
    // - **Heap**:
    //     - Stores values of dynamic sizes.
    //     - Slightly slower.
    //     - No guarantee of memory locality.
    //     - Expandable volume.

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
    } // `i` is dropped here and the value is freed.

    // assert_eq!(i, 1);  // ERROR: `i` is undefined.

    // Every value has precisely one owner at any time.
    // An assignment transfers ownership.
    let s1 = String::from("Hello");
    let s2 = s1;
    assert_eq!(s2, "Hello");
    // assert_eq!(s1, "Hello");  // ERROR: `s1` no longer owns the value.

    // Passing a value to a function also transfers ownership.
    fn consume(_: String) {
        ()
    }
    let name = String::from("Alice");
    assert_eq!(name, "Alice");
    consume(name);
    // assert_eq!(name, "Alice");  // ERROR: Ownership transferred from `name`
    //                             // to the function parameter.
    let name = String::from("Bob");
    consume(name.clone()); // Need to pass by copy explicitly.
    assert_eq!(name, "Bob"); // Ok.
                             // Note that `clone()` is usually deep-copy
                             // because it needs to maintain ownership for all its data.
                             // Exceptions are for example smart pointers.

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
    assert_eq!(x, y); // Ok. `y` is a copy.

    // NOTE "Copy" and "clone" are different:
    //
    // - Copying is bit-wise copy of memory regions.
    // - Copying has no custom logic.
    // - Copying does not work on types implementing the `Drop` trait.

    // `Copy` types are typically small, trivial-to-copy data.
    // All primitive types are `Copy`s: they copy by default.
    // For custom structs that store only primitive values,
    // you can opt in to `Copy`.

    // Implement `Drop` trait to run code when they go out of scope.
    // To run the code before the end of the scope, call `drop(obj)`.
}

// --------------------------------------------------------------------------------

#[cfg(test)]
mod exercise_builder {
    #![allow(unused)]

    #[derive(Debug, PartialEq)]
    enum Language {
        Rust,
        Java,
        Perl,
    }

    #[derive(Clone, Debug, PartialEq)]
    struct Dependency {
        name: String,
        version_expression: String,
    }

    /// A representation of a software package.
    #[derive(Debug, Default, PartialEq)]
    struct Package {
        name: String,
        version: String,
        authors: Vec<String>,
        dependencies: Vec<Dependency>,
        language: Option<Language>,
    }

    impl Package {
        /// Return a representation of this package as a dependency, for use in
        /// building other packages.
        fn as_dependency(&self) -> Dependency {
            Dependency {
                name: self.name.clone(),
                version_expression: self.version.clone(),
            }
        }
    }

    /// A builder for a Package. Use `build()` to create the `Package` itself.
    struct PackageBuilder(Package);

    impl PackageBuilder {
        fn new(name: impl Into<String>) -> Self {
            Self(Package { name: name.into(), ..Package::default() })
        }

        /// Set the package version.
        fn version(mut self, version: impl Into<String>) -> Self {
            self.0.version = version.into();
            self
        }

        /// Set the package authors.
        fn authors(mut self, authors: Vec<String>) -> Self {
            self.0.authors = authors;
            self
        }

        /// Add an additional dependency.
        fn dependency(mut self, dependency: Dependency) -> Self {
            self.0.dependencies.push(dependency);
            self
        }

        /// Set the language. If not set, language defaults to None.
        fn language(mut self, language: Language) -> Self {
            self.0.language = Some(language);
            self
        }

        fn build(self) -> Package {
            self.0
        }
    }

    // Tests

    #[test]
    fn test_builder() {
        let base64 = PackageBuilder::new("base64").version("0.13").build();
        assert_eq!(
            base64,
            Package {
                name: String::from("base64"),
                version: String::from("0.13"),
                authors: vec![],
                dependencies: vec![],
                language: None
            }
        );
        let log = PackageBuilder::new("log")
            .version("0.4")
            .language(Language::Rust)
            .build();
        assert_eq!(
            log,
            Package {
                name: String::from("log"),
                version: String::from("0.4"),
                authors: vec![],
                dependencies: vec![],

                language: Some(Language::Rust)
            }
        );
        let serde = PackageBuilder::new("serde")
            .authors(vec!["djmitche".into()])
            .version(String::from("4.0"))
            .dependency(base64.as_dependency())
            .dependency(log.as_dependency())
            .build();
        assert_eq!(
            serde,
            Package {
                name: String::from("serde"),
                version: String::from("4.0"),
                authors: vec![String::from("djmitche")],
                dependencies: vec![
                    Dependency {
                        name: String::from("base64"),
                        version_expression: String::from("0.13")
                    },
                    Dependency {
                        name: String::from("log"),
                        version_expression: String::from("0.4")
                    }
                ],
                language: None
            }
        );
    }
}

// --------------------------------------------------------------------------------

fn boxes() {
    // `Box` is an owned pointer to data on the heap.
    // Similar to `std::unique_ptr` in C++, but cannot be null.

    // Recursive data types need to use a `Box`.
    // Data types with dynamic sizes need to use a `Box`.
    // `Box` also helps you transfer ownership of large data, without the need to copy.

    #[derive(Debug)]
    enum List<T> {
        /// A non-empty list: first element and the rest of the list.
        Element(T, Box<List<T>>),
        /// An empty list.
        Nil,
    }

    let list: List<i32> = List::Element(1, Box::new(List::Element(2, Box::new(List::Nil))));
    assert_eq!(format!("{list:?}"), "Element(1, Element(2, Nil))");
}

// --------------------------------------------------------------------------------

fn reference_counted_pointer() {
    // Use `Rc` when refering to the same data from multiple places.

    use std::rc::Rc;

    let a = Rc::new(10);
    let b = Rc::clone(&a);

    assert_eq!(*a, 10);
    assert_eq!(*b, 10);

    // Compiler doesn't free the data until the count goes to 0.

    // NO mutable, because it's shared.
}

// --------------------------------------------------------------------------------

fn trait_objects() {
    // `dyn` pointer, or a fat pointer.
    // Use `dyn` pointer to specify a type that is a trait (instead of a concrete type);

    #[allow(unused)]
    struct Dog {
        name: String,
        age: i8,
    }
    #[allow(unused)]
    struct Cat {
        lives: i8,
    }

    trait Pet {
        fn talk(&self) -> String;
    }

    impl Pet for Dog {
        fn talk(&self) -> String {
            format!("Woof, my name is {}!", self.name)
        }
    }

    impl Pet for Cat {
        fn talk(&self) -> String {
            String::from("Miau!")
        }
    }

    let dog = Dog { name: String::from("Fido"), age: 3 };
    let dyn_pet: &dyn Pet = &dog;
    // let dyn_pet: dyn Pet = dog; // ERROR: Can NOT have a `dyn` by value.
    //                             // Must be a ref (pointer).
    assert_eq!(dyn_pet.talk(), "Woof, my name is Fido!");

    let pets: Vec<Box<dyn Pet>> = vec![
        Box::new(Cat { lives: 9 }),
        Box::new(Dog { name: String::from("Fido"), age: 5 }),
    ];
    assert_eq!(pets[0].talk(), "Miau!");
    assert_eq!(pets[1].talk(), "Woof, my name is Fido!");

    // `impl Trait` can only a function parameter or return type.
    // it cannot be used to hold variables.
    // The compiler infers the actual type at compile time.
    // The `dyn` trait objects have dynamic types resolved at run time.

    // println!("{}", pets[0].name); // ERROR: Cannot access fields from struct.
    //                               // Can only look up in the `Trait` definition.
}

// --------------------------------------------------------------------------------

#[cfg(test)]
mod exercise_binary_tree {
    #![allow(unused)]

    /// A node in the binary tree.
    #[derive(Debug)]
    struct Node<T: Ord> {
        value: T,
        left: Subtree<T>,
        right: Subtree<T>,
    }

    /// A possibly-empty subtree.
    #[derive(Debug)]
    struct Subtree<T: Ord>(Option<Box<Node<T>>>);

    /// A container storing a set of values, using a binary tree.
    ///
    /// If the same value is added multiple times, it is only stored once.
    #[derive(Debug)]
    pub struct BinaryTree<T: Ord> {
        root: Subtree<T>,
    }

    // Implement `new`, `insert`, `len`, and `has`.
    impl<T: Ord> Subtree<T> {
        fn insert(&mut self, v: T) {
            match &mut self.0 {
                None => {
                    self.0 = Some(Box::new(Node {
                        value: v,
                        left: Subtree(None),
                        right: Subtree(None),
                    }));
                }
                Some(node) => match v.cmp(&node.value) {
                    std::cmp::Ordering::Equal => { /* pass */ }
                    std::cmp::Ordering::Less => node.left.insert(v),
                    std::cmp::Ordering::Greater => node.right.insert(v),
                },
            }
        }

        fn len(&self) -> usize {
            match &self.0 {
                None => 0,
                Some(node) => 1 + node.left.len() + node.right.len(),
            }
        }

        fn has(&self, v: &T) -> bool {
            match &self.0 {
                None => false,
                Some(node) => match v.cmp(&node.value) {
                    std::cmp::Ordering::Equal => true,
                    std::cmp::Ordering::Less => node.left.has(v),
                    std::cmp::Ordering::Greater => node.right.has(v),
                },
            }
        }
    }

    impl<T: Ord> BinaryTree<T> {
        fn new() -> Self {
            Self { root: Subtree(None) }
        }

        fn insert(&mut self, v: T) {
            self.root.insert(v);
        }

        fn len(&self) -> usize {
            self.root.len()
        }

        fn has(&self, v: &T) -> bool {
            self.root.has(v)
        }
    }

    #[test]
    fn len() {
        let mut tree = BinaryTree::new();
        assert_eq!(tree.len(), 0);
        tree.insert(2);
        assert_eq!(tree.len(), 1);
        tree.insert(1);
        assert_eq!(tree.len(), 2);
        tree.insert(2); // not a unique item
        assert_eq!(tree.len(), 2);
    }

    #[test]
    fn has() {
        let mut tree = BinaryTree::new();
        fn check_has(tree: &BinaryTree<i32>, exp: &[bool]) {
            let got: Vec<bool> = (0..exp.len()).map(|i| tree.has(&(i as i32))).collect();
            assert_eq!(&got, exp);
        }

        check_has(&tree, &[false, false, false, false, false]);
        tree.insert(0);
        check_has(&tree, &[true, false, false, false, false]);
        tree.insert(4);
        check_has(&tree, &[true, false, false, false, true]);
        tree.insert(4);
        check_has(&tree, &[true, false, false, false, true]);
        tree.insert(3);
        check_has(&tree, &[true, false, false, true, true]);
    }

    #[test]
    fn unbalanced() {
        let mut tree = BinaryTree::new();
        for i in 0..100 {
            tree.insert(i);
        }
        assert_eq!(tree.len(), 100);
        assert!(tree.has(&50));
    }
}

// --------------------------------------------------------------------------------

fn borrowing_a_value() {
    #![allow(unused)]
    // Refs don't outlive the data.
    // You can have:
    // - one or more shared immutable references to a value
    // - exactly one exclusive mutable reference to a value

    let mut vec = vec![0, 1, 2];
    let item = &vec[2];
    // vec.push(3);  // ERROR: This mutates `vec` while `item` borrows it.
    //               // If this was allowed, there is a chance that
    //               // the push reallocates the vector data (for expansion)
    //               // leaving the `item` referencing to an obsolete address.

    // `Cell` lets you set the value with multiple `&Cell` references.
    // It does this by never allowing you to access references of the value:
    // whenever you access the value, you get a copy.

    // `RefCell` moves the restriction from compile time to run time.
}

// --------------------------------------------------------------------------------

#[cfg(test)]
mod exercise_health_stats {
    #![allow(unused)]

    pub struct User {
        name: String,
        age: u32,
        height: f32,
        visit_count: usize,
        last_blood_pressure: Option<(u32, u32)>,
    }

    pub struct Measurements {
        height: f32,
        blood_pressure: (u32, u32),
    }

    pub struct HealthReport<'a> {
        // `'a` is a "life-time parameter".
        patient_name: &'a str,
        visit_count: u32,
        height_change: f32,
        blood_pressure_change: Option<(i32, i32)>,
    }

    impl User {
        pub fn new(name: String, age: u32, height: f32) -> Self {
            Self {
                name,
                age,
                height,
                visit_count: 0,
                last_blood_pressure: None,
            }
        }

        pub fn visit_doctor(&mut self, measurements: Measurements) -> HealthReport {
            self.visit_count += 1;
            let report = HealthReport {
                patient_name: &self.name,
                visit_count: (self.visit_count as u32),
                height_change: measurements.height - self.height,
                blood_pressure_change: match self.last_blood_pressure {
                    None => None,
                    Some(blood_pressure) => Some((
                        measurements.blood_pressure.0 as i32 - blood_pressure.0 as i32,
                        measurements.blood_pressure.1 as i32 - blood_pressure.1 as i32,
                    )),
                },
            };
            self.height = measurements.height;
            self.last_blood_pressure = Some(measurements.blood_pressure);
            report
        }
    }

    #[test]
    fn test_visit() {
        let mut bob = User::new(String::from("Bob"), 32, 155.2);
        assert_eq!(bob.visit_count, 0);
        let report = bob.visit_doctor(Measurements { height: 156.1, blood_pressure: (120, 80) });
        assert_eq!(report.patient_name, "Bob");
        assert_eq!(report.visit_count, 1);
        assert_eq!(report.blood_pressure_change, None);

        let report = bob.visit_doctor(Measurements { height: 156.1, blood_pressure: (115, 76) });

        assert_eq!(report.visit_count, 2);
        assert_eq!(report.blood_pressure_change, Some((-5, -4)));
    }
}

// --------------------------------------------------------------------------------

fn lifetime_annotations() {
    // The lifetime of a borrow must be shorter than the lifetime of the underlying data.
    // NOTE: Specify lifetimes only when the compiler asks you to.

    // Each function, implicitly or explicitly, has a lifetime associated with it.
    // When the compiler cannot infer the lifetime,
    // you are required to explicitly specify it.

    #[derive(Debug)]
    struct Point(i32, i32);

    // Compiler doesn't know if you are returning `p1` or `p2`,
    // so it cannot decide automatically the lifetime of the returned value.
    // fn left_most(p1: &Point, p2: &Point) -> &Point {  // ERROR
    fn left_most<'a>(p1: &'a Point, p2: &'a Point) -> &'a Point {
        if p1.0 < p2.0 {
            p1
        } else {
            p2
        }
    }
    let p1: Point = Point(10, 10);
    let p2: Point = Point(20, 20);
    let p3 = left_most(&p1, &p2); // Either `&p1` or `&p2` will be returned.
    assert_eq!(format!("{p3:p}"), format!("{:p}", &p1)); // Same address.

    // fn foo<'a, 'b: 'a>(...) { ... }  // This means `'b` must out-live `'a`.

    // For methods, the compiler always assumes that
    // the lifetime of the returned reference to be the lifetime of `self`.
    // For regular functions, the assumptions vary depending on the function signature.

    // `struct`s also have lifetimes.

    // NOTE Try having your `struct`s own all the data when possible,
    // unless the data are too expenssive to copy.
    // Because if a `struct` has reference fields,
    // you might need to specify their lifetimes.
}

// --------------------------------------------------------------------------------

#[cfg(test)]
mod exercise_protobuf_parsing {
    #![allow(unused)]

    use std::convert::TryFrom;
    use thiserror::Error;

    #[derive(Debug, Error)]
    enum Error {
        #[error("Invalid varint")]
        InvalidVarint,
        #[error("Invalid wire-type")]
        InvalidWireType,
        #[error("Unexpected EOF")]
        UnexpectedEOF,
        #[error("Invalid length")]
        InvalidSize(#[from] std::num::TryFromIntError),
        #[error("Unexpected wire-type)")]
        UnexpectedWireType,
        #[error("Invalid string (not UTF-8)")]
        InvalidString,
    }

    /// A wire type as seen on the wire.
    enum WireType {
        /// The Varint WireType indicates the value is a single VARINT.
        Varint,
        //I64,  -- not needed for this exercise
        /// The Len WireType indicates that the value is a length represented as a
        /// VARINT followed by exactly that number of bytes.
        Len,
        /// The I32 WireType indicates that the value is precisely 4 bytes in
        /// little-endian order containing a 32-bit signed integer.
        I32,
    }

    #[derive(Debug)]
    /// A field's value, typed based on the wire type.
    enum FieldValue<'a> {
        Varint(u64),
        //I64(i64),  -- not needed for this exercise
        Len(&'a [u8]),
        I32(i32),
    }

    #[derive(Debug)]
    /// A field, containing the field number and its value.
    struct Field<'a> {
        field_num: u64,
        value: FieldValue<'a>,
    }

    trait ProtoMessage<'a>: Default + 'a {
        fn add_field(&mut self, field: Field<'a>) -> Result<(), Error>;
    }

    impl TryFrom<u64> for WireType {
        type Error = Error;

        fn try_from(value: u64) -> Result<WireType, Error> {
            Ok(match value {
                0 => WireType::Varint,
                //1 => WireType::I64,  -- not needed for this exercise
                2 => WireType::Len,
                5 => WireType::I32,
                _ => return Err(Error::InvalidWireType),
            })
        }
    }

    impl<'a> FieldValue<'a> {
        fn as_string(&self) -> Result<&'a str, Error> {
            let FieldValue::Len(data) = self else {
                return Err(Error::UnexpectedWireType);
            };
            std::str::from_utf8(data).map_err(|_| Error::InvalidString)
        }

        fn as_bytes(&self) -> Result<&'a [u8], Error> {
            let FieldValue::Len(data) = self else {
                return Err(Error::UnexpectedWireType);
            };
            Ok(data)
        }

        fn as_u64(&self) -> Result<u64, Error> {
            let FieldValue::Varint(value) = self else {
                return Err(Error::UnexpectedWireType);
            };
            Ok(*value)
        }
    }

    /// Parse a VARINT, returning the parsed value and the remaining bytes.
    fn parse_varint(data: &[u8]) -> Result<(u64, &[u8]), Error> {
        for i in 0..7 {
            let Some(b) = data.get(i) else {
                return Err(Error::InvalidVarint);
            };
            if b & 0x80 == 0 {
                // This is the last byte of the VARINT, so convert it to
                // a u64 and return it.
                let mut value = 0u64;
                for b in data[..=i].iter().rev() {
                    value = (value << 7) | (b & 0x7f) as u64;
                }
                return Ok((value, &data[i + 1..]));
            }
        }

        // More than 7 bytes is invalid.
        Err(Error::InvalidVarint)
    }

    /// Convert a tag into a field number and a WireType.
    fn unpack_tag(tag: u64) -> Result<(u64, WireType), Error> {
        let field_num = tag >> 3;
        let wire_type = WireType::try_from(tag & 0x7)?;
        Ok((field_num, wire_type))
    }

    /// Parse a field, returning the remaining bytes
    fn parse_field(data: &[u8]) -> Result<(Field, &[u8]), Error> {
        let (tag, remainder) = parse_varint(data)?;
        let (field_num, wire_type) = unpack_tag(tag)?;
        let (fieldvalue, remainder) = match wire_type {
            WireType::Varint => {
                let (value, remainder) = parse_varint(remainder)?;
                (FieldValue::Varint(value), remainder)
            }
            WireType::Len => {
                let (len, remainder) = parse_varint(remainder)?;
                let len = usize::try_from(len)?;
                if remainder.len() < len {
                    return Err(Error::UnexpectedEOF);
                }
                let (value, remainder) = remainder.split_at(len);
                (FieldValue::Len(value), remainder)
            }
            WireType::I32 => {
                if remainder.len() < 4 {
                    return Err(Error::UnexpectedEOF);
                }
                let (value, remainder) = remainder.split_at(4);
                let value = i32::from_le_bytes(value.try_into().unwrap());
                (FieldValue::I32(value), remainder)
            }
        };
        Ok((Field { field_num, value: fieldvalue }, remainder))
    }

    /// Parse a message in the given data, calling `T::add_field` for each field in
    /// the message.
    ///
    /// The entire input is consumed.
    fn parse_message<'a, T: ProtoMessage<'a>>(mut data: &'a [u8]) -> Result<T, Error> {
        let mut result = T::default();
        while !data.is_empty() {
            let parsed = parse_field(data)?;
            result.add_field(parsed.0)?;
            data = parsed.1;
        }
        Ok(result)
    }

    #[derive(Debug, Default, PartialEq)]
    struct PhoneNumber<'a> {
        number: &'a str,
        type_: &'a str,
    }

    #[derive(Debug, Default, PartialEq)]
    struct Person<'a> {
        name: &'a str,
        id: u64,
        phone: Vec<PhoneNumber<'a>>,
    }

    // TODO: Implement ProtoMessage for Person and PhoneNumber.
    impl<'a> ProtoMessage<'a> for Person<'a> {
        fn add_field(&mut self, field: Field<'a>) -> Result<(), Error> {
            match field.field_num {
                1 => self.name = field.value.as_string()?,
                2 => self.id = field.value.as_u64()?,
                3 => self.phone.push(parse_message(field.value.as_bytes()?)?),
                _ => { /* pass */ }
            }
            Ok(())
        }
    }

    impl<'a> ProtoMessage<'a> for PhoneNumber<'a> {
        fn add_field(&mut self, field: Field<'a>) -> Result<(), Error> {
            match field.field_num {
                1 => self.number = field.value.as_string()?,
                2 => self.type_ = field.value.as_string()?,
                _ => { /* pass */ }
            }
            Ok(())
        }
    }

    #[test]
    fn test() {
        let person: Person = parse_message(&[
            0x0a, 0x07, 0x6d, 0x61, 0x78, 0x77, 0x65, 0x6c, 0x6c, 0x10, 0x2a, 0x1a, 0x16, 0x0a,
            0x0e, 0x2b, 0x31, 0x32, 0x30, 0x32, 0x2d, 0x35, 0x35, 0x35, 0x2d, 0x31, 0x32, 0x31,
            0x32, 0x12, 0x04, 0x68, 0x6f, 0x6d, 0x65, 0x1a, 0x18, 0x0a, 0x0e, 0x2b, 0x31, 0x38,
            0x30, 0x30, 0x2d, 0x38, 0x36, 0x37, 0x2d, 0x35, 0x33, 0x30, 0x38, 0x12, 0x06, 0x6d,
            0x6f, 0x62, 0x69, 0x6c, 0x65,
        ])
        .unwrap();
        assert_eq!(
            person,
            Person {
                name: "maxwell",
                id: 42,
                phone: vec![
                    PhoneNumber { number: "+1202-555-1212", type_: "home" },
                    PhoneNumber { number: "+1800-867-5308", type_: "mobile" },
                ]
            }
        );
    }
}

// --------------------------------------------------------------------------------

fn iterators() {
    struct Fibonacci {
        curr: u32,
        next: u32,
    }

    impl Iterator for Fibonacci {
        type Item = u32;

        fn next(&mut self) -> Option<Self::Item> {
            let new_next = self.curr + self.next;
            self.curr = self.next;
            self.next = new_next;
            Some(self.curr)
        }
    }

    let fib = Fibonacci { curr: 0, next: 1 };
    let mut result = String::new();
    for (i, n) in fib.enumerate().take(5) {
        result.push_str(&format!("fib({i}): {n}\n"));
    }
    assert_eq!(
        result,
        "\
    fib(0): 1\n\
    fib(1): 1\n\
    fib(2): 2\n\
    fib(3): 3\n\
    fib(4): 5\n\
    "
    );

    // Implement the `IntoIterator` trait
    // to create an iterator from an object.
    // This is how `for` loops work too.

    struct Grid {
        width: u32,
        height: u32,
    }
    impl IntoIterator for Grid {
        type Item = (u32, u32);
        type IntoIter = GridIter;
        fn into_iter(self) -> Self::IntoIter {
            GridIter { grid: self, x: 0, y: 0 }
        }
    }
    struct GridIter {
        grid: Grid,
        x: u32,
        y: u32,
    }
    impl Iterator for GridIter {
        type Item = (u32, u32);
        fn next(&mut self) -> Option<Self::Item> {
            // Steps:
            // 1. Validate
            // 2. Get current value
            // 3. Advance internal state for next iteration

            // Validate.
            if self.x >= self.grid.width || self.y >= self.grid.height {
                return None;
            }
            // Return value for current iteration.
            let res = Some((self.x, self.y));
            // Advance internal state for next iteration.
            self.x += 1;
            if self.x >= self.grid.width {
                self.y += 1; // Don't worry about validation ---
                             // that's done on the next iteration.
                self.x = 0;
            }
            res
        }
    }

    let grid = Grid { width: 3, height: 4 };
    let mut output = String::new();
    for (x, y) in grid {
        output.push_str(&format!("({x}, {y})\n"));
    }
    assert_eq!(
        output,
        "\
    (0, 0)\n\
    (1, 0)\n\
    (2, 0)\n\
    (0, 1)\n\
    (1, 1)\n\
    (2, 1)\n\
    (0, 2)\n\
    (1, 2)\n\
    (2, 2)\n\
    (0, 3)\n\
    (1, 3)\n\
    (2, 3)\n\
    "
    );
    // println!("{:?}", grid); // ERROR: Note How `into_iter` consumes `self`.
    //                         // So `grid` is no longer available.
    //                         // To avoid consumption,
    //                         // `impl IntoIterator for &Grid` instead.

    // Implementing `FromIterator` allows
    // building a collection from an `Iterator`
    // using the `collect()` method.
    let numbers = vec![1, 2, 3, 4];
    let numbers_squared = numbers.iter().map(|n| n * n).collect::<Vec<_>>();
    // Or:
    // let numbers_squared: Vec<_> = numbers.iter().map(|n| n*n).collect();
    assert_eq!(numbers_squared, vec![1, 4, 9, 16]);

    // `Iterator` provides many functional data streaming methods:
    // - `fold()` (simalar to `reduce()` but more powerful)
    // - `map()`
    // - `filter()`, `filter_map()`
    // - 'zip()' and `unzip()`
}

// --------------------------------------------------------------------------------

#[cfg(test)]
mod exercise_iterator_method_chaining {
    #![allow(unused)]

    /// Calculate the differences between elements of `values` offset by `offset`,
    /// wrapping around from the end of `values` to the beginning.
    ///
    /// Element `n` of the result is `values[(n+offset)%len] - values[n]`.
    fn offset_differences<N>(offset: usize, values: Vec<N>) -> Vec<N>
    where
        N: Copy + std::ops::Sub<Output = N>,
    {
        values
            .iter()
            .zip(values.iter().cycle().skip(offset))
            .map(|(&cur, &off)| off - cur)
            .collect()
    }

    #[test]
    fn test_offset_one() {
        assert_eq!(offset_differences(1, vec![1, 3, 5, 7]), vec![2, 2, 2, -6]);
        assert_eq!(offset_differences(1, vec![1, 3, 5]), vec![2, 2, -4]);
        assert_eq!(offset_differences(1, vec![1, 3]), vec![2, -2]);
    }

    #[test]
    fn test_larger_offsets() {
        assert_eq!(offset_differences(2, vec![1, 3, 5, 7]), vec![4, 4, -4, -4]);
        assert_eq!(offset_differences(3, vec![1, 3, 5, 7]), vec![6, -2, -2, -2]);
        assert_eq!(offset_differences(4, vec![1, 3, 5, 7]), vec![0, 0, 0, 0]);
        assert_eq!(offset_differences(5, vec![1, 3, 5, 7]), vec![2, 2, 2, -6]);
    }

    #[test]
    fn test_custom_type() {
        assert_eq!(
            offset_differences(1, vec![1.0, 11.0, 5.0, 0.0]),
            vec![10.0, -6.0, -5.0, 1.0]
        );
    }

    #[test]
    fn test_degenerate_cases() {
        assert_eq!(offset_differences(1, vec![0]), vec![0]);
        assert_eq!(offset_differences(1, vec![1]), vec![0]);
        let empty: Vec<i32> = vec![];
        assert_eq!(offset_differences(1, empty), vec![]);
    }
}

// --------------------------------------------------------------------------------

fn modules() {
    // Modules are like namespaces.

mod outer {
    #![allow(unused)]

    fn private() -> i32 {
        1
    }
    pub fn public() -> i32 {
        2
    }

    mod private_inner {
        fn private() -> i32 {
            3
        }
        pub fn public() -> i32 {
            self::private() /* 3 */ + super::private() /* 1 */
        }
    }

    pub(crate) mod crate_accessible_inner {
        fn private() -> i32 {
            // super::private_inner::private() // ERROR.
            5
        }
        pub fn public() -> i32 {
            2 + super::private_inner::public() /* 4 */
        }
    }
}

    // assert_eq!(outer::private(), 1); // ERROR.
    //                                  // Cannot access private functions in a module.
    assert_eq!(outer::public(), 2);
    // assert_eq!(outer::private_inner::public(), 4); // ERROR.
    assert_eq!(outer::crate_accessible_inner::public(), 6);

    // Crates are a tree of modules.
    // Use `cargo` commands to build creates.
    // The file system tree of a crate looks like this:
    //
    // .
    // ├── Cargo.lock
    // ├── Cargo.toml  // Project/crate configuration.
    // ├── target/
    // │   └── ...  // Generated files.
    // └── src/
    //     ├── main.rs  // Executable entry point.
    //     ├── garden.rs  // A module called `garden`.
    //     ├── garden/
    //     │   └── garden/vegetables.rs  // Module `garden::vegetables`.
    //     └── house/
    //         ├── mod.rs  // Module `house`.
    //         └── tables.rs // Module `house::tables`.
    //
    // Rust will look for these files
    // when you include a module
    // using `mod garden;`
    //
    // Alternatively, you can specify the path explicitly:
    // ```
    // #[path="some/path.rs"]
    // mod my_module;
    // ```

    // To import symbols from another module, write
    // ```
    // use std::collections::HashSet;
    // ```
    // To re-export the symbol to users of this module, write
    // ```
    // pub use std::collections::HashSet;
    // ```

    mod mycollections {
        #[allow(unused)]
        use std::collections::HashSet;
        pub use std::collections::HashMap;
    }
    // let _: mycollections::HashSet<u32>;  // ERROR. `HashSet` is private in `mycollections`.
    let _: mycollections::HashMap<u32, u32>;
}

// --------------------------------------------------------------------------------

fn unit_tests() {
    // #[test]
    // fn a_test_function() {}

    // // Test modules are only included when running tests.
    // #[cfg(test)]
    // mod a_test_module {
    //     #[test]
    //     fn a_test_function() {}
    // }

    // #[test]
    // #[should_panic]
    // fn test_error() {
    //     let nums = vec![1, 2];
    //     nums[3];
    // }

    // #[test]
    // fn test() -> Result<(), String> {
    //     Ok(())
    // }

    // // Write tests directly under implementations.
}

// --------------------------------------------------------------------------------

fn integration_tests() {
    // Create a `tests` folder next to `src`.
    // These are blackbox tests
    // because they no longer have access to private functions
    // from the module under test.
}

// --------------------------------------------------------------------------------

fn documentation_tests() {
    #[allow(unused)]
    /// Shortens a string to the given length.
    ///
    /// ```
    /// # use playground::shorten_string;
    /// assert_eq!(shorten_string("Hello World", 5), "Hello");
    /// assert_eq!(shorten_string("Hello World", 20), "Hello World");
    /// ```
    pub fn shorten_string(s: &str, length: usize) -> &str {
        &s[..std::cmp::min(length, s.len())]
    }

    // These tests will both
    // render in documentation
    // and run on `cargo test`.
    // The `#` hides the code from the doc but still gets run.

    // Code blocks can be annotated, for exampl:
    // - ```ignore
    // - ```no_run
    // - ```should_panic
    // - ```compile_fail
}

// --------------------------------------------------------------------------------

fn lint_and_clippy() {
    // Clippy (https://doc.rust-lang.org/clippy/) offers additional lints.
    // Use the `#[deny(some-lint)]` attribute to disable a lint
    // for the specified item.
}

// --------------------------------------------------------------------------------

#[cfg(test)]
mod exercise_lhun_algorithm {
    #![allow(unused)]

    pub fn luhn(cc_number: &str) -> bool {
        let Some(digits): Option<Vec<u32>> = (cc_number.chars().rev())
            .filter(|c| !c.is_whitespace()) // Ignore whitespaces.
            .map(|c| c.to_digit(10))
            .collect()
        else {
            return false; // Cannot contain non-digit non-whitespace chars.
        };
        if digits.len() < 2 {
            return false;
        }
        let sum: u32 = (digits.iter().copied().step_by(2)) // Single digits.
            .chain(
                (digits.iter().skip(1).step_by(2)) // Double digits.
                    .map(|n| (n * 2) / 10 + (n * 2) % 10),
            )
            .sum();
        sum % 10 == 0
    }

    #[test]
    fn test_valid_cc_number() {
        assert!(luhn("4263 9826 4026 9299"));
        assert!(luhn("4539 3195 0343 6467"));
        assert!(luhn("7992 7398 713"));
        assert!(luhn("6 1 2 3 4"));
    }

    #[test]
    fn test_invalid_cc_number() {
        assert!(!luhn("4223 9826 4026 9299"));
        assert!(!luhn("4539 3195 0343 6476"));
        assert!(!luhn("8273 1232 7352 0569"));
        assert!(!luhn("01"));
    }

    #[test]
    fn test_too_short_cc_number() {
        assert!(!luhn("0"));
        assert!(!luhn(" 0 "));
        assert!(!luhn("1"));
    }

    #[test]
    fn test_double_over_10() {
        assert!(luhn("91"));
        assert!(luhn("380"));
        assert!(luhn("174"));
        assert!(luhn("67"));
        assert!(luhn("59"));
    }

    #[test]
    fn test_sum_over_10() {
        assert!(luhn("919191919191919191919191"));
        assert!(luhn("838383838383838383838383"));
    }

    #[test]
    fn test_invalid_characters() {
        assert!(!luhn("bar0"));
    }

    #[test]
    fn test_empty_number() {
        assert!(!luhn(""));
        assert!(!luhn(" "));
        assert!(!luhn("  "));
    }
}

// --------------------------------------------------------------------------------

fn error_handling() {
    // Use a combination of `Result<_, _>` and the try operator `?`.

    // The try operator also tries to convert the unwrapped error into the expected error type.
    // When the type conversion does not exsit,
    // you can `impl From<>` yourself.

    // To write your own Error type,
    // it's recommended to use `thiserror::Error`
    // because it helps implement `Display` and `From`.

    #[derive(Debug, thiserror::Error)]
    #[error("This is an error: {0:?}")] // This will be the message of the error.
    struct MyError(String);

    // `thiserror::Error` also allows `enum` errors (for a family of errors).

    // Use the `anyhow` crate to pretend all errors are the same type
    // (so you don't have to decide for each function).

    fn this_is_to_catch_the_error_returned_by_the_try_operator() -> Result<(), anyhow::Error> {
        use anyhow::bail;
        fn vector_or_error() -> anyhow::Result<Vec<i32>> {
            bail!("You ain't getting no vector!"); // This returns an `anyhow::Error`.
        }
        use anyhow::Context;
        let _sum: i32 = vector_or_error()
            .with_context(|| {
                MyError(String::from(
                    "I'm trying to do this when calling this function",
                ))
            })? // `with_context` prepends to the error (if any).
            .iter()
            .sum();
        Ok(())
    }
    let Err(_) = this_is_to_catch_the_error_returned_by_the_try_operator() else {
        panic!()
    };
}

// --------------------------------------------------------------------------------

#[cfg(test)]
mod exercise_result {
    #![allow(unused)]

    use anyhow::bail;
    use std::iter::Peekable;
    use std::str::Chars;

    /// An arithmetic operator.
    #[derive(Debug, PartialEq, Clone, Copy)]
    enum Op {
        Add,
        Sub,
    }

    /// A token in the expression language.
    #[derive(Debug, PartialEq)]
    enum Token {
        Number(String),
        Identifier(String),
        Operator(Op),
    }

    /// An expression in the expression language.
    #[derive(Debug, PartialEq)]
    enum Expression {
        /// A reference to a variable.
        Var(String),
        /// A literal number.
        Number(u32),
        /// A binary operation.
        Operation(Box<Expression>, Op, Box<Expression>),
    }

    fn tokenize(input: &str) -> Tokenizer {
        return Tokenizer(input.chars().peekable());
    }

    #[derive(thiserror::Error, Clone, Debug, PartialEq)]
    #[error("Unexpected character '{0}' in in put")]
    struct TokenizerError(String);

    struct Tokenizer<'a>(Peekable<Chars<'a>>);

    impl<'a> Iterator for Tokenizer<'a> {
        type Item = Result<Token, TokenizerError>;

        fn next(&mut self) -> Option<Result<Token, TokenizerError>> {
            let c = self.0.next()?;
            match c {
                '0'..='9' => {
                    let mut num = String::from(c);
                    while let Some(c @ '0'..='9') = self.0.peek() {
                        num.push(*c);
                        self.0.next();
                    }
                    Some(Ok(Token::Number(num)))
                }
                'a'..='z' => {
                    let mut ident = String::from(c);
                    while let Some(c @ ('a'..='z' | '_' | '0'..='9')) = self.0.peek() {
                        ident.push(*c);
                        self.0.next();
                    }
                    Some(Ok(Token::Identifier(ident)))
                }
                '+' => Some(Ok(Token::Operator(Op::Add))),
                '-' => Some(Ok(Token::Operator(Op::Sub))),
                _ => Some(Err(TokenizerError(format!("Unexpected character {c}")))),
            }
        }
    }

    fn parse(input: &str) -> anyhow::Result<Expression> {
        let mut tokens = tokenize(input);

        fn parse_expr<'a>(tokens: &mut Tokenizer<'a>) -> anyhow::Result<Expression> {
            let Some(tok) = tokens.next().transpose()? else {
                bail!("Unexpected end of input");
            };
            let expr = match tok {
                Token::Number(num) => {
                    let v = num.parse().expect("Invalid 32-bit integer'");
                    Expression::Number(v)
                }
                Token::Identifier(ident) => Expression::Var(ident),
                Token::Operator(_) => bail!("Unexpected token {tok:?}"),
            };
            // Look ahead to parse a binary operation if present.
            match tokens.next().transpose()? {
                None => Ok(expr),
                Some(Token::Operator(op)) => Ok(Expression::Operation(
                    Box::new(expr),
                    op,
                    Box::new(parse_expr(tokens)?),
                )),
                Some(tok) => bail!("Unexpected token {tok:?}"),
            }
        }

        parse_expr(&mut tokens)
    }

    #[test]
    fn test() {
        let expr = parse("10+foo+20-30");
        assert_eq!(
            expr.unwrap(),
            Expression::Operation(
                Box::new(Expression::Number(10)),
                Op::Add,
                Box::new(Expression::Operation(
                    Box::new(Expression::Var(String::from("foo"))),
                    Op::Add,
                    Box::new(Expression::Operation(
                        Box::new(Expression::Number(20)),
                        Op::Sub,
                        Box::new(Expression::Number(30))
                    ))
                ))
            )
        );
        let expr = parse("10+");
        if let Err(_) = expr {
        } else {
            assert!(false)
        };
    }
}

// --------------------------------------------------------------------------------

fn unsafe_rust() {
    // To write unsafe Rust, put code in (small) `unsafe` blocks and justify with comments.
    // Unsafe Rust can trigger undefined behavior.
    // Unsafe Rust lets you:
    //
    // - Dereference raw pointers.
    // - Access or modify mutable static variables.
    // - Access `union` fields.
    // - Call `unsafe` functions, including `extern` functions.
    // - Implement `unsafe` traits.

    let r1 = &mut String::from("careful") as *mut String;
    // println!("{}", *r1); // ERROR: Cannot dereference a raw pointer.
    unsafe {
        assert_eq!(format!("{}", *r1), "careful");
    }

    // `i` and `b` are stored on the same byte on heap.
    #[allow(unused)]
    union MyUnion {
        i: u8,
        b: bool,
    }
    let u = MyUnion { i: 42 };
    // assert_eq!(format!("int: {}", u.i), "int: 42"); // ERROR: Cannot decide whether `i` or `b` is
    //                                                 // stored.
    assert_eq!(format!("int: {}", unsafe { u.i }), "int: 42");
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
    boxes();
    reference_counted_pointer();
    trait_objects();
    borrowing_a_value();
    lifetime_annotations();
    // Day 4:
    iterators();
    modules();
    unit_tests();
    integration_tests();
    documentation_tests();
    lint_and_clippy();
    error_handling();
    unsafe_rust();
}
