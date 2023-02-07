/// An intepreter for a simple query language allowing for combining comparison operations with `AND`
/// E.g. (birth_date > 18) AND (birth_date <= 50)
/// Attrubutes are encoded by numbers and assumed to be resolved from human-redable at a pre-processing stage

use dep::std;

global MAX_QUERY_SIZE: u8 = 20;
global MAX_NUM_OF_ATTRS: u8 = 20;

// codes for attrubutes
global DATE_OF_BIRTH: u8 = 0;

// codes for operations
global EQ: u4 = 0;
global LEQ: u4 = 1;
global GT: u4 = 2;
global STOP: u4 = 15; // max u4

struct BinOp {
      kind: u4,
      attribute: u8, // an ecoding of an attribute
      val: Field, // a value to compate the attribute to
  }

impl BinOp {
    fn new(k: u4, a: u8, v: Field ) -> Self {
        BinOp { kind: k, attribute: a, val: v }
    }
}

struct PrivateClaimInfo {
    attrs: [Field; MAX_NUM_OF_ATTRS], // a tuple of attribute values
    randomness: [Field; MAX_NUM_OF_ATTRS] // a tuple of random secrets
  }

// Ideally, we would use array of `BinOp` here, that is `[BinOp]`,
// but noir does not allow for array of structs/tuples.
// So, we can use an isomorphic representation: i-th element of each array
// correponds to a `BinOp` instance.
struct AndQuery {
    ops: [u4; MAX_QUERY_SIZE],
    attrs: [u8; MAX_QUERY_SIZE],
    vals: [Field; MAX_QUERY_SIZE],
}

// This looks silly, but it allows for using a runtime (computed) `u8` value to be used for indexing
// Noir restricts indices to compile-time values.
fn runtime_index(xs: [Field], i: u8) -> Field {
    let n = std::array::len(xs); // length is known in compile-time
    constrain i <= n as u8; // fail if out of bounds
    let mut res = 0;
    for j in 0..n-1 { // `j` ranges from `0` to a compile-time value `n-1`
        if j as u8 == i {
            res = xs[j];
        }
    }
    res
}

// There are two `Field` values for each commitment.
// Since Noir does not support array of structs/tuples/arrays we just store the pairs in one flat array
fn get_commitment(xs: [Field; MAX_NUM_OF_ATTRS * 2], i: u8) -> [Field;2] {
    let v0 = runtime_index(xs, i*2);
    let v1 = runtime_index(xs, i*2+1);
    [v0, v1]
}


fn iterp_bin_op(op: BinOp, claim: PrivateClaimInfo) -> bool {
    if (op.kind == EQ) & (op.attribute == DATE_OF_BIRTH) {
        (op.val as i32) == (claim.attrs[0] as i32)
    } else {
        if (op.kind == LEQ) & (op.attribute == DATE_OF_BIRTH) {
        (op.val as i32) <= (claim.attrs[0] as i32)
        } else {
            if (op.kind == GT) & (op.attribute == DATE_OF_BIRTH) {
            (op.val as i32) > (claim.attrs[0] as i32)
            } else {
                false
            }
        }
    }
}

fn get_private_data(claim: PrivateClaimInfo, i: u8) -> (Field, Field) {
    (runtime_index(claim.attrs, i), runtime_index(claim.randomness, i))
}


/// The main function takes
///   public data: a query, a vector of committments
///   private data: claim info containing attrubute values and random secrets.
fn main(query: pub AndQuery,
        com_vec: pub [Field; MAX_NUM_OF_ATTRS * 2], // vector of commitments pairs `(Field, Field)` are stored in a flat array
        claim: PrivateClaimInfo) {
    let mut res: bool = true;
    let mut stop_flag: bool = false;
    let n = std::array::len(query.ops);
    for i in 0..n-1 {
       if (query.ops[i] == STOP) | stop_flag {
           // if hit STOP, set the stop_flag so the rest of the loop is just constraining to the same `res`
           // NOTE: it seems there is no way of exiting the loop in Noir
           stop_flag = true;
           constrain res;
       } else {
           let attr_index = query.attrs[i];
           let (v, secret) = get_private_data(claim, attr_index);
           let v_comm = get_commitment(com_vec, attr_index);
            // first check that `v` opens `v_comm`
           constrain std::hash::pedersen([v, secret]) == v_comm;
           // then compute the accumulated AND and check whether it's `true` 
           res = res & iterp_bin_op(BinOp::new(query.ops[i], query.attrs[i], query.vals[i]), claim);
       }
    }
    constrain res;
}
