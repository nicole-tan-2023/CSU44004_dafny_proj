
/*** Even ***/

 ghost predicate isEven(n: int) {
  exists m: int :: n == 2 * m
}
lemma EvenModulo(n: int)
  ensures isEven(n) ==> n % 2 == 0
{}
lemma ModuloEven(n: int)
  ensures n % 2 == 0 ==> isEven(n)
{
	if n % 2 == 0 {
	  var m := n / 2;
	  assert n == 2 * m;
	}
}
function checkEven(n: int) : (b: bool) {
	n % 2 == 0
}
lemma checkEvenCorrect(n: int)
  ensures checkEven(n) <==> isEven(n)
{
	EvenModulo(n);
	ModuloEven(n);
}
lemma EvenTimes(n1: int, n2: int)
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
function checkOdd(n: int): (b: bool) {
	n % 2 != 0
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
  if isOdd(n1) && isOdd(n2) {
    var m1 := n1 / 2;
    var m2 := n2 / 2;
    assert n1 * n2 == 2 * (2 * m1 * m2 + m1 + m2) + 1;
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
  if n % 2 == 0 {
	ModuloEven(n);
  } else {
	ModuloOdd(n);
  }
}

lemma EvenTimesOdd(n1: int, n2: int)
  ensures isEven(n1) && isOdd(n2) ==> isEven(n1 * n2)
{
  if isEven(n1) && isOdd(n2) {
    var m1 := n1 / 2;
    var m2 := n2 / 2;
    assert n1 * n2 == 2 * (2 * m1 * m2 + m1);
  }
}

function invertParity(n: int): (m: int) {
	n + 1
}

lemma InvertParityCorrect(n: int)
  ensures isEven(n) ==> isOdd(invertParity(n))
  ensures isOdd(n) ==> isEven(invertParity(n))
{
	if isEven(n) {
		var m := invertParity(n);
		ModuloOdd(m);
	} else {
		var m := invertParity(n);
		ModuloEven(m);
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
 isSet(s) && forall x :: x in s ==> isEven(x)
}

method checkEvenSet(s: seq<int>) returns (b: bool)
  ensures b <==> isEvenSet(s)
{
  b := true;
  var i := 0;
  while (i < |s| && b)
    invariant 0 <= i <= |s|
    invariant b ==> isEvenSet(s[..i])
    invariant b <== isEvenSet(s[..i])
    invariant b <==> (isSet(s[..i]) && (forall j :: 0 <= j < i ==> checkEven(s[j])))
  {
    // Dafny hint that isEven <==> checkEven
    checkEvenCorrect(s[i]);
    //* [REPORT] Moved the isSet and checkEven checks into the same while loop
    //* while less efficient - it helps a lot in reducing the complexity of the
    //* invariants. Otherwise, we needed to keep track of the 2 ways b could be
    //* false: when it's not a set, and when there's an odd elements.
    if (!isSet(s[..i+1]) || !checkEven(s[i])) {
      b := false;
    }
    i := i + 1;
  }
}

/* An odd set is a set where all elements are odd */
ghost predicate isOddSet(s: seq<int>) {
  isSet(s) && forall x :: x in s ==> isOdd(x)
}

method checkOddSet(s: seq<int>) returns (b: bool)
  ensures b <==> isOddSet(s)
{
  b := true;
  var i := 0;
  while (i < |s| && b)
    invariant 0 <= i <= |s|
    invariant b ==> isOddSet(s[..i])
    invariant b <== isOddSet(s[..i])
    invariant b <==> (isSet(s[..i]) && (forall j :: 0 <= j < i ==> checkOdd(s[j])))
  {
    checkOddCorrect(s[i]);
    //* [REPORT] Moved the isSet and checkOdd checks into the same while loop
    //* Same reasoning as checkOddSet
    if (!isSet(s[..i+1]) || !checkOdd(s[i])) {
      b := false;
    }
    i := i + 1;
  }
}


/*** Set Operations ***/

/* Adds n to a set s, making sure it remains a set */
// Hint: use recursion
method addToSet(s: seq<int>, n: int) returns (b: seq<int>)
  requires isSet(s)
  ensures isSet(b)
  ensures forall x :: (0 <= x < |b|) ==> (b[x] in s || b[x] == n)
  ensures forall x :: (0 <= x < |s|) ==>  s[x] in b
  ensures n in s ==> b == s
  ensures !(n in s) ==> b == s + [n]
  ensures isEvenSet(s) && isEven(n) ==> isEvenSet(b)
  ensures isOddSet(s) && isOdd(n) ==> isOddSet(b)
  ensures n !in s ==> |b| == |s| + 1 // [REPORT] Added to help formal verify the other questions
{
 if n in s {
    b := s;
  }
  else {
    b := s + [n];
  } 
}

/* unions two sets s1 and s2, returning a new set t */
method union(s1: seq<int>, s2: seq<int>) returns (t: seq<int>)
  requires isSet(s1) && isSet(s2)
  ensures isSet(t)
  ensures forall x :: (0 <= x < |t| ==> t[x] in s1 || t[x] in s2)
  ensures forall x :: (0 <= x < |s1| ==> s1[x] in t)
  ensures forall x :: (0 <= x < |s2| ==> s2[x] in t)
  ensures isEvenSet(s1) && isEvenSet(s2) ==> isEvenSet(t)
  ensures isOddSet(s1) && isOddSet(s2) ==> isOddSet(t)
{
  t := s1;
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
}


/* intersects two sets s1 and s2, returning a new set t */
method intersection(s1: seq<int>, s2: seq<int>) returns (t: seq<int>)
  requires isSet(s1) && isSet(s2)
  ensures isSet(t)
  ensures forall x :: (0 <= x < |t| ==> t[x] in s1 && t[x] in s2)
  ensures forall x, y :: (0 <= x < |s1| && 0 <= y < |s2| && s1[x] == s2[y]) ==> s1[x] in t
  ensures isEvenSet(s1) ==> isEvenSet(t)
  ensures isOddSet(s1) ==> isOddSet(t)
  ensures isEvenSet(s1) && isOddSet(s2) ==> |t| == 0
{
  // hint: you may need to call:
  //  NotEvenANDOdd(s1[i]);
  // at the appropriate place in your code to help Dafny prove correctness
  t := [];
  var i := 0;
  while i < |s1|
    invariant 0 <= i <= |s1|
    invariant isSet(t)
    invariant forall k :: 0 <= k < i ==> (s1[k] in s2) ==> (s1[k] in t)
    //* The above invariant ensures dafny that we have checked that any element 
    //* in s1[0..max(i-1,0)] that is in s2 has been added to t
    invariant forall z :: (z in t) ==> (z in s1) && (z in s2)
    invariant isEvenSet(s1) && isOddSet(s2) ==> |t| == 0
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
      invariant isEvenSet(s1) && isOddSet(s2) ==> |t| == 0
    {
      // Hints to help dafny
      NotEvenANDOdd(s1[i]);
      assert isEvenSet(s1) && isOddSet(s2) ==> isEven(s1[i]) && isOdd(s2[j]);
      assert isEvenSet(s1) && isOddSet(s2) ==> s1[i] != s2[j];
      if s1[i] == s2[j] {
        t := addToSet(t, s1[i]);
      }
      j := j + 1;
    }
    i := i + 1;
  }
  
}

// [REPORT] This one is tedious to do because we needed to remember to define
// invariants for the while loop so that dafny knows that t == s[..i]
/* difference of two sets s1 and s2, returning a new set t = s1 - s2 */
method difference(s1: seq<int>, s2: seq<int>) returns (t: seq<int>)
  requires isSet(s1) && isSet(s2)
  ensures isSet(t)
  ensures forall x :: (0 <= x < |t| ==> t[x] in s1 && !(t[x] in s2))
  ensures forall x :: (0 <= x < |s1| && !(s1[x] in s2)) ==> s1[x] in t
  ensures isEvenSet(s1) ==> isEvenSet(t)
  ensures isOddSet(s1) ==> isOddSet(t)
  ensures isEvenSet(s1) && isOddSet(s2) ==> t == s1 // hint: don't use addToSet in your code -- use t + [s1[i]] instead
{
  //* The logic behind the proof of these set operations are similar to the ones above. 
  //* We will just talk about the new things to note here.
  t := [];
  var i := 0;
  while i < |s1|
    invariant 0 <= i <= |s1|
    invariant isSet(s1)
    invariant isSet(t)
    invariant forall k :: 0 <= k < i ==> (s1[k] !in s2) ==> (s1[k] in t)
    invariant forall z :: (z in t) ==> (z in s1) && (z !in s2)
    invariant forall x :: x in t ==> x in s1[..i]
    invariant isEvenSet(s1) && isOddSet(s2) ==> |s1[..i]| == |t|
    invariant isEvenSet(s1) && isOddSet(s2) ==> forall j :: 0 <= j < i ==> s1[j] == t[j]
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
      invariant isEvenSet(s1) && isOddSet(s2) ==> !foundInS2
    {
      NotEvenANDOdd(s1[i]);
      assert isEvenSet(s1) && isOddSet(s2) ==> !foundInS2; 
      assert isEvenSet(s1) && isOddSet(s2) ==> isEven(s1[i]) && isOdd(s2[j]);
      assert isEvenSet(s1) && isOddSet(s2) ==> s1[i] != s2[j];
      if s1[i] == s2[j] {
        foundInS2 := true;
      }
      j := j + 1;
    }
    assert isEvenSet(s1) && isOddSet(s2) ==> !foundInS2;
    if !foundInS2 { 
      NotEvenANDOdd(s1[i]);
      assert isSet(t);
      assert forall x :: x in t ==> x in s1;
      assert (s1[i] !in t);
      t := t + [s1[i]];
      assert isSet(t);
    }
    i := i + 1;
  }
  assert isEvenSet(s1) && isOddSet(s2) ==> |t| == |s1|;
  assert isEvenSet(s1) && isOddSet(s2) ==> t == s1;
}


// [REPORT] Learnt that something we need to comment out stuff in dafny. otherwise TLE. 
// Theory vs Practical diff. For instance, we already got everything correct,
// but we just needed to comment out the asserts that are slowing everything down.
// With this we learnt to write proof for each PC one at a time, removing the asserts 
// afterwards. We only keep the ones that are necessary.
// Also, so this method, we decided to move the edge case checking up top
// This is to simplify the logic of the checking in the main while loop. Elaborate more ty.
/* multiplies each element of a set s by n, returning a new set t */
method setScale(s: seq<int>, n: int) returns (t: seq<int>)
  requires isSet(s)
  ensures isSet(t)
  ensures forall x :: (0 <= x < |t| ==> exists j :: 0 <= j < |s| && t[x] == s[j] * n)
  ensures forall x :: (0 <= x < |s| ==> s[x] * n in t)
  ensures isEvenSet(s) || isEven(n) ==> isEvenSet(t)
  ensures isOddSet(s) && isOdd(n) ==> isOddSet(t)
{
  // hint: you may need to call:
  //  EvenTimes(s[i], n);
  //  OddTimesOdd(s[i], n);
  // at the appropriate place in your code to help Dafny prove correctness
  t := [];
  if |s| == 0 {
    return t;
  }
  if n == 0 {
    t := [0];
    checkEvenCorrect(0);
    assert (forall x :: (0 <= x < |t| ==> exists j :: 0 <= j < |s| && t[x] == s[j] * n)) by {
      assert n == 0;
      assert forall x :: 0 <= x < |t| ==> t[x] == s[0] * n;
      assert forall x :: 0 <= x < |t| ==> exists j :: 0 <= j < |s| && t[x] == s[j] * n;
    }

    assert forall x :: (0 <= x < |s| ==> s[x] * n in t);
    return t;
  }

  assert |s| > 0 && n != 0;
  
  var i := 0;
  while i < |s|
    invariant isSet(t)
    invariant 0 <= i <= |s|
    invariant |t| == i
    invariant forall x :: (0 <= x < i) ==> s[x] * n in t
    invariant forall x :: (0 <= x < i) ==> t[x] == s[x] * n
    invariant isEven(n) ==> isEvenSet(t)
    invariant isEvenSet(s) ==> isEvenSet(t)
    invariant isOddSet(s) && isOdd(n) ==> isOddSet(t)
  {
    
    OddTimesOdd(n, s[i]);
    EvenTimes(n, s[i]);
    t := addToSet(t, n * s[i]);
  
    i := i + 1;
  }
  // [REPORT] Removed asserts example
  // assert isOddSet(s) && isOdd(n) ==> isOddSet(t);
  // assert forall x :: (0 <= x < |s|) ==> t[x] == s[x] * n;
  // assert forall x :: (0 <= x < |t| ==> exists j :: 0 <= j < |s| && t[x] == s[j] * n);
  // assert forall x :: (0 <= x < |s| ==> s[x] * n in t);

  // assert |s| == |t|;

  // assert isEven(n) ==> isEvenSet(t);
  // assert isEvenSet(s) ==> isEvenSet(t);
}


// TODO: This method up to you already Nicole 💀
// [REPORT] Rewrote this to avoid double while loops.
// Instead we use proved procedures to simplify proof.
// Learnt here that dafny does better with indexed access
method setProduct(s1: seq<int>, s2: seq<int>) returns (t: seq<int>)
  requires isSet(s1) && isSet(s2)
  ensures isSet(t)
  ensures forall x :: x in t ==> exists i1, j1 :: 0 <= i1 < |s1| && 0 <= j1 < |s2| && x == s1[i1] * s2[j1]
  ensures forall i1, j1 :: i1 in s1 && j1 in s2 ==> i1 * j1 in t
  ensures isEvenSet(s1) || isEvenSet(s2) ==> isEvenSet(t)
  ensures isOddSet(s1) && isOddSet(s2) ==> isOddSet(t)
{
  t := [];
  var i := 0;

  while i < |s1|
    invariant isSet(t)
    invariant 0 <= i <= |s1|
    invariant forall k, j :: 0 <= k < i && 0 <= j < |s2| ==> s1[k] * s2[j] in t
  {
    var s3 := setScale(s2, s1[i]);  
    assert isEvenSet(s1) || isEvenSet(s2) ==> isEvenSet(s3);
    assert isOddSet(s1) && isOddSet(s2) ==> isOddSet(s3);
    assert forall z :: z in s3 ==> exists j :: 0 <= j < |s2| && z == s1[i] * s2[j];

    t := union(t, s3);

    // Now s3 elements are in t (usually trivial if union is specified)
    assert forall z :: z in s3 ==> z in t;
    assert isEvenSet(s1) || isEvenSet(s2) ==> isEvenSet(t);
    assert isOddSet(s1) && isOddSet(s2) ==> isOddSet(t);

    // advance to next iteration — now the invariant with k < i will include i-old
    i := i + 1;
  }

  // At loop exit, i == |s1|, so the invariant "forall k < i" covers all k in 0..|s1|-1
  // Prove the final postcondition explicitly if Dafny still needs help:
  assert forall x :: x in t ==> exists i1, j1 :: 0 <= i1 < |s1| && 0 <= j1 < |s2| && x == s1[i1] * s2[j1];
}



// [REPORT] This method is easy for us because we already wrecked our brains thinking of
// How do do the one for setScale. We notice that after the boundary conditions in setscale
// we basically have the same while loop body of t := addToSet(t, value).
// This immediately tells us that we will need some of the invariants of the loop in setScale
/* converts an even set to an odd set by inverting the parity of each element  */
method invertParitySet(s: seq<int>) returns (t:seq<int>)
  requires isEvenSet(s) || isOddSet(s)
  ensures isEvenSet(s) ==> isOddSet(t)
  ensures isOddSet(s) ==> isEvenSet(t)
  ensures |t| == |s|
  ensures forall i :: 0 <= i < |s| ==> t[i] == invertParity(s[i])
{
  t := [];
  var i := 0;
  while i < |s|
    invariant isSet(t)
    invariant 0 <= i <= |s|
    invariant |t| == i
    invariant forall j :: 0 <= j < i ==> t[j] == invertParity(s[j])
    invariant isEvenSet(s) ==> isOddSet(t)
    invariant isOddSet(s) ==> isEvenSet(t)
  {
    InvertParityCorrect(s[i]);
    t := addToSet(t, invertParity(s[i]));
    i := i + 1;
  }
}
