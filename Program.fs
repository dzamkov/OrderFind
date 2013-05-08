module Program

/// Represents a polynomial in one variable.
type Polynomial private (coefficients : bigint[]) =
    
    /// The zero polynomial.
    static member Zero = Polynomial Array.empty

    /// Creates a polynomial with the given coefficients.
    static member Create (coefficients : bigint[]) =
        let mutable firstNotZero = coefficients.Length - 1
        while firstNotZero >= 0 && coefficients.[firstNotZero].IsZero do firstNotZero <- firstNotZero - 1
        if firstNotZero = coefficients.Length - 1 then Polynomial coefficients
        elif firstNotZero >= 0 then
            let nCoefficients = Array.zeroCreate (firstNotZero + 1)
            Array.blit coefficients 0 nCoefficients 0 nCoefficients.Length
            Polynomial nCoefficients
        else Polynomial.Zero

    /// Creates a polynomial for a constant value.
    static member Constant (value : bigint) =
        if value.IsZero then Polynomial.Zero
        else Polynomial [| value |]

    /// Creates a polynomial for the variable raised to a certain power.
    static member Power (power : int) =
        let coefficients = Array.zeroCreate (power + 1)
        coefficients.[power] <- 1I
        Polynomial coefficients
    
    /// Gets the coefficients for this polynomial.
    member this.Coefficients = coefficients

    /// Gets the degree of this polynomial.
    member this.Degree = max 0 (coefficients.Length - 1)

    /// Evaluates this polynomial for the given parameter.
    member this.Evaluate parameter =
        let mutable result = bigint.Zero
        let mutable power = 1I
        for i = 0 to coefficients.Length - 1 do
            result <- result + coefficients.[i] * power
            power <- power * parameter
        result

    /// Evaluates this polynomial for the given parameter in a modular ring.
    member this.EvaluateMod modulus parameter =
        let mutable result = bigint.Zero
        let mutable power = 1I
        for i = 0 to coefficients.Length - 1 do
            result <- result + coefficients.[i] * power
            power <- (power * parameter) % modulus
        ((result % modulus) + modulus) % modulus

    /// Adds two polynomials together.
    static member (+) (a : Polynomial, b : Polynomial) =
        let coefficients = Array.zeroCreate (max a.Coefficients.Length b.Coefficients.Length)
        Array.blit a.Coefficients 0 coefficients 0 a.Coefficients.Length
        for i = 0 to b.Coefficients.Length - 1 do
            coefficients.[i] <- coefficients.[i] + b.Coefficients.[i]
        Polynomial.Create coefficients

    /// Subtracts one polynomial from another.
    static member (-) (a : Polynomial, b : Polynomial) =
        let coefficients = Array.zeroCreate (max a.Coefficients.Length b.Coefficients.Length)
        Array.blit a.Coefficients 0 coefficients 0 a.Coefficients.Length
        for i = 0 to b.Coefficients.Length - 1 do
            coefficients.[i] <- coefficients.[i] - b.Coefficients.[i]
        Polynomial.Create coefficients

    /// Multiplies two polynomials together.
    static member (*) (a : Polynomial, b : Polynomial) =
        let coefficients = Array.create (a.Coefficients.Length * b.Coefficients.Length) bigint.Zero
        for i = 0 to a.Coefficients.Length - 1 do
            for j = 0 to b.Coefficients.Length - 1 do
                coefficients.[i + j] <- coefficients.[i + j] + a.Coefficients.[i] * b.Coefficients.[j]
        Polynomial.Create coefficients

    /// Divides one polynomial by another, returning the quotient and remainder.
    static member DivRem (n : Polynomial) (d : Polynomial) =
        if n.Coefficients.Length < d.Coefficients.Length then (Polynomial.Zero, n)
        else
            let qefficients = Array.zeroCreate (n.Coefficients.Length - d.Coefficients.Length + 1)
            let refficients = Array.copy n.Coefficients
            let dLead = d.Coefficients.[d.Coefficients.Length - 1]
            for i = qefficients.Length - 1 downto 0 do
                let rLeadIndex = i + d.Coefficients.Length - 1
                let q = bigint.DivRem (refficients.[rLeadIndex], dLead, &refficients.[rLeadIndex])
                qefficients.[i] <- q
                for j = 0 to d.Coefficients.Length - 2 do
                    refficients.[i + j] <- refficients.[i + j] - d.Coefficients.[j] * q
            (Polynomial.Create qefficients, Polynomial.Create refficients)

    /// Divides one polynomial by another, returning the quotient.
    static member (/) (n : Polynomial, d : Polynomial) =
        fst (Polynomial.DivRem n d)

    /// Divides one polynomial by another, returning the remainder.
    static member (%) (n : Polynomial, d : Polynomial) =
        snd (Polynomial.DivRem n d)


/// Contains functions related to polynomials.
[<CompilationRepresentation(CompilationRepresentationFlags.ModuleSuffix)>]
module Polynomial =

    /// The zero polynomial.
    let zero = Polynomial.Zero

    /// Constructs a constant polynomial.
    let cons value = Polynomial.Constant value
    
    /// Constructs a polynomial for the variable raised to a certain power.
    let power power = Polynomial.Power power

    /// Constructs a polynomial that evaluates to zero for an n-th root of unity.
    let uzero n = power n - cons 1I

    /// Constructs a polynomial that evaluates to zero for a k-th root of unity where k is
    /// between a and b (inclusive).
    let uzeroRange a b = [for i = a to b do yield uzero i] |> List.reduce (*)

    /// Evaluates a polynomial for a given parameter.
    let eval (polynomial : Polynomial) parameter = polynomial.Evaluate parameter

    /// Evaluates a polynomial for a given parameter in a modular integer ring.
    let evalMod modulus (polynomial : Polynomial) parameter = polynomial.EvaluateMod modulus parameter

    /// Divides one polynomial by another, returning the returning the quotient and remainder.
    let divRem n d = Polynomial.DivRem n d

[<EntryPoint>]
let main args =
    let poly = Polynomial.uzeroRange 1 14
    let lower = Polynomial.uzeroRange 1 7
    let upper, r1 = Polynomial.divRem poly lower // Polynomial.uzeroRange 8 14
    let upperq, r2 = Polynomial.divRem upper lower
    let eval m x =
        let lower = Polynomial.evalMod m lower x
        let upperq = Polynomial.evalMod m upperq x
        let upper = (lower * upperq) % m
        (lower * upper) % m

    let x = Polynomial.evalMod 17I poly 3I
    let y = eval 17I 3I
    0