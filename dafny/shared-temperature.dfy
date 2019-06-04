
function method avg(x: int, y: int): int
{
    (x + y) / 2
}

function method max(x: int, y: int): int { if x < y then y else x }

function method min(x: int, y: int): int { if x < y then x else y }

function method constrain(a: int, b: int, x: int): int
    requires a <= b
    ensures a <= constrain(a, b, x) <= b
{
    max(a, min(b, x))
}

// ---------------------------------------------------

type temperature = int

datatype range = Range(a: temperature, b: temperature)

predicate is_range(r: range) { r.a <= r.b }

function method singleton(t: temperature): range
    ensures is_range(singleton(t))
{
    Range(t, t)
}

function method range_avg(r: range): temperature
    requires is_range(r)
    ensures r.a <= range_avg(r) <= r.b
{
    avg(r.a, r.b)
}

function method range_distance_from(t: temperature, r: range): nat
    requires is_range(r)
{
    if      t < r.a then r.a - t
    else if r.b < t then t - r.b
    else                 0
}

// ---------------------------------------------------

function method shared_range(t: temperature, x: range, y: range): range
    requires is_range(x) && is_range(y)
    ensures is_range(shared_range(t, x, y))
{
    var a := max(x.a, y.a);
    var b := min(x.b, y.b);
    if a <= b
    then Range(a, b)
    else singleton(constrain(b, a, t))
}

lemma sr_comm(t: temperature, x: range, y: range)
    requires is_range(x) && is_range(y)
    ensures shared_range(t, x, y) == shared_range(t, y, x)
{}

lemma sr_assoc(t: temperature, x: range, y: range, z: range)
    requires is_range(x) && is_range(y) && is_range(z)
    ensures shared_range(t, shared_range(t, x, y), z)
            ==
            shared_range(t, x, shared_range(t, y, z))
{}

// ---------------------------------------------------

function method shared_temperature(t: temperature, x: range, y: range): temperature
    requires is_range(x) && is_range(y)
{
    range_avg(shared_range(t, x, y))
}

lemma st_comm(t: temperature, x: range, y: range)
    requires is_range(x) && is_range(y)
    ensures shared_temperature(t, x, y)
            ==
            shared_temperature(t, y, x)
{
    sr_comm(t, x, y);
}

function total_distance_from(t: temperature, x: range, y: range): nat
    requires is_range(x) && is_range(y)
{
    range_distance_from(t, x) + range_distance_from(t, y)
}

lemma st_as_good_as_any(t: temperature, x: range, y: range, alt: temperature)
    requires is_range(x) && is_range(y)
    ensures total_distance_from(shared_temperature(t, x, y), x, y)
            <=
            total_distance_from(alt, x, y)
{}

lemma st_no_advantage_to_lying(t: temperature, x: range, x_lie: range, y: range)
    requires is_range(x) && is_range(x_lie) && is_range(y)
    ensures range_distance_from(shared_temperature(t, x, y), x)
            <=
            range_distance_from(shared_temperature(t, x_lie, y), x)
{}

// ---------------------------------------------------
