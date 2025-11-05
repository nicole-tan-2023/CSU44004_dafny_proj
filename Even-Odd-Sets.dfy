
/*** Even ***/

ghost predicate isEven(n: int) {
  exists m: int :: n == 2 * m
}
function checkEven(n: int) : (b: bool) {
	n % 2 == 0
}
// The next three lemmas prove that modulo-based definition is equivalent to existential-based definition
lemma EvenModulo(n: int)
  ensures isEven(n) ==> n % 2 == 0
{}
lemma ModuloEven(n: int)
  ensures n % 2 == 0 ==> isEven(n)
{
	if n % 2 == 0 {
	  var m := n / 2;
	  assert n == 2 * m; // Hint for Dafny to choose n/2 as witness for the existential in the isEven predicate
	}
}
lemma checkEvenCorrect(n: int)
  ensures checkEven(n) <==> isEven(n)
{
	EvenModulo(n);
	ModuloEven(n);
}
// Useful lemma that may be used later
// It shows that the product of two integers is even if at least one of them is even
lemma EvenTimesAny(n1: int, n2: int)
  ensures isEven(n1) || isEven(n2) ==> isEven(n1 * n2)
{
  if isEven(n1) {
	  var m1 := n1 / 2;
	  assert n1 * n2 == 2 * (m1 * n2);
  } else if isEven(n2) {
	  var m2 := n2 / 2;
	  assert n1 * n2 == 2 * (n1 * m2);
  }
}

/*** Odd ***/

ghost predicate isOdd(n: int) {
  exists m: int :: n == 2 * m + 1
}
function checkOdd(n: int): (b: bool) {
	n % 2 != 0
}
lemma OddModulo(n: int)
  ensures isOdd(n) ==> n % 2 != 0
{}
lemma ModuloOdd(n: int)
  ensures n % 2 != 0 ==> isOdd(n)
{ 
  if n % 2 != 0 {
    var m := n / 2;
    assert n == 2 * m + 1;
  }
}
lemma checkOddCorrect(n: int)
  ensures checkOdd(n) <==> isOdd(n)
{
  OddModulo(n);
  ModuloOdd(n);
}
lemma OddTimesOdd(n1: int, n2: int)
  ensures isOdd(n1) && isOdd(n2) ==> isOdd(n1 * n2)
{
  if isOdd(n1) && isOdd(n2){
    // var m1 := n1 / 2;
    // var m2 := n2 / 2;
    var m1 :| n1 == 2 * m1 + 1;
    var m2 :| n2 == 2 * m2 + 1;
    assert n1 * n2 == 2 * (2 *m1 * m2 + m1 + m2) + 1;
    assert isOdd(n1 * n2);
  }
}

/*** Even & Odd ***/

lemma NotEvenANDOdd(n: int)
  ensures !(isEven(n) && isOdd(n))
{ 
}

lemma EvenOrOdd(n: int)
  ensures isEven(n) || isOdd(n)
{
  if isEven(n) {
    assert isEven(n) || isOdd(n);
  }
  else {
    var m := n / 2;
    assert n == 2 * m + 1;
    assert isOdd(n);
    assert isEven(n) || isOdd(n);
  }
}

lemma EvenTimesOdd(n1: int, n2: int)
  ensures isEven(n1) && isOdd(n2) ==> isEven(n1 * n2)
{
  if (isEven(n1)){
    var m := n1 / 2;
    assert n1 * n2 == 2 * (m * n2);
    assert isEven(n1 * n2);
  }
}

function invertParity(n: int): (m: int) {
	n + 1
}

lemma InvertParityCorrect(n: int)
  ensures isEven(n) ==> isOdd(invertParity(n))
  ensures isOdd(n) ==> isEven(invertParity(n))
{
  if (isEven(n)){
    var m :| n == 2 * m;
    assert invertParity(n) == 2 * m + 1;
  }
  else {
    EvenOrOdd(n);
    var m :| n == 2 * m + 1;
    assert invertParity(n) == 2 * (m + 1);
  }
}


/*** Even and Odd Sets ***/

/* A set is represented as a sequence with no duplicates */
predicate isSet(s: seq<int>) {
  forall i,j: int :: 0 <= i < j < |s| ==> 
  s[j] != s[i]
}

// hint don't use return statements. Set b instead.
method checkSet(s: seq<int>) returns (b: bool)
  ensures b <==> isSet(s)
{
  b := true;
  var i := 0;
  while (i < |s| && b) //* We use && b here, and in the inner while loop in order to "break out" of the while loop when we find a duplicate. 
    invariant 0 <= i <= |s|
    invariant b <==> forall x, y :: 0 <= x < y < i ==> s[x] != s[y]
  {
    assert b <==> forall x, y :: 0 <= x < y < i ==> s[x] != s[y];
    var j := i - 1;
    while (j >= 0 && b)
      invariant -1 <= j < i
      invariant b <==> forall k :: j < k < i ==> s[k] != s[i] 
      invariant b ==> forall x, y :: 0 <= x < y < i ==> s[x] != s[y] 
      //* We do not need the <== direction because it won't hold once b is set to false.
      //* As such, we use && b to break out of this inner loop.
      //* This ensures dafny that in the outer loop, when b is set to false,
      //* When i := i + 1 gets executed we get a F ==> T for the invariant
      //* forall x, y :: 0 <= x < y < i ==> s[x] != s[y] ==> b
      //* at the end of the loop.
    {
      if s[i] == s[j]{
        b := false;
      }
      j := j - 1;
    }
    assert b <==> forall k :: 0 <= k < i ==> s[k] != s[i];
    i := i + 1;
    assert b <==> forall x, y :: 0 <= x < y < i ==> s[x] != s[y];
  }
  assert b <==> isSet(s);
}


/* An even set is a set where all elements are even */
ghost predicate isEvenSet(s: seq<int>) {
  isSet(s) && forall i :: 0 <= i < |s| ==> isEven(s[i])
  // isSet(s) && forall i :: 0 <= i < |s| ==> checkEven(s[i])
}

method checkEvenSet(s: seq<int>) returns (b: bool)
  ensures b <==> isEvenSet(s)
{
  b := true;
  var i := 0;
  while (i < |s| && b)
    invariant 0 <= i <= |s|
    invariant b <==> (forall j :: 0 <= j < i ==> checkEven(s[j]))
  {
    if (!checkEven(s[i])) {
      b := false;
    }
    i := i + 1;
  }
  if !isSet(s) {
    b := false;
    // return b;
  }
  //* Dafny needs help recognising the equivalance of isEven and checkEven over a sequence.
  assert (forall j :: 0 <= j < i ==> checkEven(s[j])) 
    <==> (forall j :: 0 <= j < i ==> 2 * (s[j] / 2) == s[j]);
  assert b <== isEvenSet(s);
  assert b ==> isEvenSet(s);
}

/* An odd set is a set where all elements are odd */
ghost predicate isOddSet(s: seq<int>) {
  isSet(s) && forall i :: 0 <= i < |s| ==> isOdd(s[i])
  // isSet(s) && forall i :: 0 <= i < |s| ==> checkOdd(s[i])
}

method checkOddSet(s: seq<int>) returns (b: bool)
  ensures b <==> isOddSet(s)
{
  b := true;
  var i := 0;
  while (i < |s| && b)
    invariant 0 <= i <= |s|
    invariant b <==> (forall j :: 0 <= j < i ==> checkOdd(s[j]))
  {
    if (!checkOdd(s[i])) {
      b := false;
    }
    i := i + 1;
  }
  if !isSet(s) {
    b := false;
  }
  //* Likewise, Dafny needs help recognising the equivalance of isOdd and checkOdd over an array.
  assert (forall j :: 0 <= j < i ==> checkOdd(s[j])) 
    <==> (forall j :: 0 <= j < i ==> 2 * (s[j] / 2) + 1== s[j]);
  assert b <== isOddSet(s);
  assert b ==> isOddSet(s);
}

/*** Set Operations ***/

// For the following methods specify their behaviour so that your specification characterizes the allowed outputs,
// and as many relevant properties of the result as you can.
// Marks will be awarded for specifying as much as possible all relevant properties of the output.

/* Adds n to a set s, making sure it remains a set */
method addToSet(s: seq<int>, n: int) returns (b: seq<int>)
  requires isSet(s)
  ensures isSet(b)  //* Without the requires statement, we want isSet(s) ==> isSet(b), 
                    //* but making this function partial seems like the better choice here.
  ensures n in b
  ensures forall x :: x in s ==> x in b
  ensures forall x :: x in b ==> x in s || x == n //* Ensures that no other element is added.
  ensures (n !in s) <==> |s| + 1 == |b| //* Equivalent to ensuring that no other elements are added and isSet(b)
  ensures n in s <==> s == b
{
  if n in s {
    b := s;
  }
  else {
    b := s + [n];
  }
  assert isSet(b);
  assert n in b;
  assert forall x :: x in s ==> x in b;
  assert forall x :: x in b ==> x in s || x == n;
  assert (n !in s) <==> |s| + 1 == |b|;
  assert n in s <==> s == b;
}

/* Unions two sets s1 and s2, returning a new set t */
method union(s1: seq<int>, s2: seq<int>) returns (t: seq<int>)
  requires isSet(s1) && isSet(s2)
  ensures isSet(t)
  ensures forall x :: (x in s1) ==> (x in t)
  ensures forall y :: (y in s2) ==> (y in t)
  ensures |s1| + |s2| >= |t| //* Sanity check bound
  ensures forall z :: z in t ==> (z in s1) || (z in s2) //* Ensures that all the elements in t only comes from s1 or s2
{
  t := s1;
  assert isSet(t);
  var i := 0;
  while i < |s2|
    invariant 0 <= i <= |s2|
    invariant isSet(t)
    invariant |s1| + |s2[0..i]| >= |t|
    invariant forall z :: z in t ==> (z in s1) || (z in s2[0..i])
    invariant forall j :: 0 <= j < i ==> s2[j] in t //* This is to help dafny check that by the end of the loop we have:
                                                    //* forall y :: y in s2 ==> y in t
                                                    //* Indexing was helpful here to avoid index out of bounds errors with seqeunce splicing
    invariant forall x :: x in s1 ==> x in t
  {
    t := addToSet(t, s2[i]);
    i := i + 1;
  }
  assert isSet(t);
  assert forall x :: (x in s1) ==> (x in t);
  assert forall y :: (y in s2) ==> (y in t);
  assert |s1| + |s2| >= |t|;
  assert forall z :: z in t ==> (z in s1) || (z in s2);
}

/* Intersects two sets s1 and s2, returning a new set t */
method intersection(s1: seq<int>, s2: seq<int>) returns (t: seq<int>)
  requires isSet(s1) && isSet(s2)
  ensures isSet(t)
  ensures forall x :: (x in s1) && (x in s2) ==> (x in t)
  ensures forall z :: (z in t) ==> (z in s1) && (z in s2) //* Ensures that every z in t can be found in both sets.
{
  t := [];
  var i := 0;
  while i < |s1|
    invariant 0 <= i <= |s1|
    invariant isSet(t)
    invariant forall k :: 0 <= k < i ==> (s1[k] in s2) ==> (s1[k] in t)
    //* The above invariant ensures dafny that we have checked that any element 
    //* in s1[0..max(i-1,0)] that is in s2 has been added to t
    invariant forall z :: (z in t) ==> (z in s1) && (z in s2)
  {
    var j := 0;
    while j < |s2|
      invariant 0 <= j <= |s2|
      invariant isSet(t)
      invariant forall k :: 0 <= k < i ==> (s1[k] in s2) ==> (s1[k] in t)
      invariant forall h :: 0 <= h < j ==> (s2[h] == s1[i]) ==> (s1[i] in t)
      //* The above invariant ensures dafny that we have checked that any element
      //* in s2[0..max(j-1,0)] that is equals to s1[i] has been added to t
      invariant forall z :: (z in t) ==> (z in s1) && (z in s2)
    {
      if s1[i] == s2[j] {
        t := addToSet(t, s1[i]);
      }
      j := j + 1;
    }
    i := i + 1;
  }
assert isSet(t);
assert forall x :: (x in s1) && (x in s2) ==> (x in t);
assert forall z :: (z in t) ==> (z in s1) && (z in s2);
}

/* Difference of two sets s1 and s2, returning a new set t = s1 - s2 */
method difference(s1: seq<int>, s2: seq<int>) returns (t: seq<int>)
  requires isSet(s1) && isSet(s2)
  ensures isSet(t)
  ensures forall x :: (x in s1) && (x !in s2) ==> (x in t)
  ensures forall z :: (z in t) ==> (z in s1) && (z !in s2)
{
  //* The logic behind the proof of these set operations are similar to the ones above. 
  //* We will just talk about the new things to note here.
  t := [];
  var i := 0;
  while i < |s1|
    invariant 0 <= i <= |s1|
    invariant isSet(t)
    invariant forall k :: 0 <= k < i ==> (s1[k] !in s2) ==> (s1[k] in t)
    invariant forall z :: (z in t) ==> (z in s1) && (z !in s2)
  {
    var foundInS2 := false;
    var j := 0;
    while j < |s2| && !foundInS2
      invariant 0 <= j <= |s2|
      invariant isSet(t)
      invariant forall k :: 0 <= k < i ==> (s1[k] !in s2) ==> (s1[k] in t)
      invariant foundInS2 <==> exists h :: 0 <= h < j && s2[h] == s1[i]
      //* The above invariant helps dafny ensure that addToSet(t, s1[i]) will only 
      //* be called iff we did not find s1[i] in s2.
    {
      if s1[i] == s2[j] {
        foundInS2 := true;
      }
      j := j + 1;
    }
    if !foundInS2 {
      assert (s1[i] !in s2);
      t := addToSet(t, s1[i]);
    }
    i := i + 1;
  }
  assert isSet(t);
  assert forall x :: (x in s1) && (x !in s2) ==> (x in t);
  assert forall z :: (z in t) ==> (z in s1) && (z !in s2);
}

/* Multiplies each element of a set s by n, returning a new set t */
method setScale(s: seq<int>, n: int) returns (t: seq<int>)
// TODO: Specify the behavior of this method so that your specification characterizes the allowed outputs,
// and as many relevant properties of the result as you can.
  requires isSet(s)
  ensures isSet(t)
  ensures forall x :: (x in s) ==> exists y :: (y in t) && (n * x == y)
  ensures forall y :: (y in t) ==> exists x :: (x in s) && (n * x == y)
  // ensures n != 0 ==> |s| == |t|
  // ensures (n == 0 && |s| != 0) ==> |t| == 1
{ // TODO: formally verify
  t := [];
  var i := 0;
  while i < |s|
    invariant isSet(t)
  {
    t := addToSet(t, n * s[i]);
    i := i + 1;
  }
}

/* Computes the product set of two sets s1 and s2, returning a new set t = { n * m | n in s1, m in s2 }  */
method setProduct(s1: seq<int>, s2: seq<int>) returns (t: seq<int>)
  requires isSet(s1) && isSet(s2)
  ensures isSet(t)
  //* For every (n,m) pair in s1 x s2, we can find mn in t
  //* This ensures all required elements are inside t.
  ensures forall x :: (x in s1) ==> forall y :: (y in s2) ==> (x*y in t) 
  //* For every z in t, we should be able to factorise it to z = xy, x in s1, y in s2.
  //* This prevents redundant elements inside t.
  ensures forall z :: (z in t) ==> exists x :: x in s1 && exists y :: y in s2 && (z == x*y)
{ // TODO: Formally verify
  t := [];
  var i := 0;
  while i < |s1|
    invariant isSet(t)
  {
    var j := 0;
    while j < |s2|
      invariant isSet(t)
    {
      t := addToSet(t, s1[i] * s2[j]);
      j := j + 1;
    }
    i := i + 1;
  }
}

/* Converts an even set to an odd set by inverting the parity of each element  
   Hint: Use the invertParity function */
method invertParitySet(s: seq<int>) returns (t:seq<int>)
// TODO: Specify the behavior of this method so that your specification characterizes the allowed outputs,
// and as many relevant properties of the result as you can.
  requires isSet(s) && isEvenSet(s)
  ensures isSet(t)
  ensures isOddSet(t)
  ensures forall x :: (x in s) ==> (invertParity(x) in t)
  ensures forall y :: (y in t) ==> (y - 1 in s) 
  //* The condition above is defined that way specifically because invertParity(n) is defined
  //* as n+1. So we simply have to reverse it to check that any element in t, is originally from s.
{
  t := [];
  var i := 0;
  while i < |s|
    invariant isSet(t)
  {
    t := addToSet(t, invertParity(s[i]));
    i := i + 1;
  }
}
