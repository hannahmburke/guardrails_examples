module Utils {

// Predicate: word containment
function Intersection(s1: seq<string>, s2: seq<string>): set<string>
{
  (set x | x in s1 :: x) * (set x | x in s2 :: x)
}

// Split by spaces
function Split(s: string): seq<string>
{
  var idx := FindSpace(s);
  if idx == |s| then [s]
  else [s[..idx]] + Split(s[idx+1..])
}

// Finds first space in string
function FindSpace(s: string): nat
  ensures FindSpace(s) <= |s|
  ensures FindSpace(s) < |s| ==> s[FindSpace(s)] == ' '
  ensures forall i :: 0 <= i < FindSpace(s) ==> s[i] != ' '
{
  FindSpaceHelper(s, 0)
}

function FindSpaceHelper(s: string, i: nat): nat
  requires i <= |s|
  ensures FindSpaceHelper(s, i) <= |s|
  ensures FindSpaceHelper(s, i) < |s| ==> s[FindSpaceHelper(s, i)] == ' '
  ensures forall j :: i <= j < FindSpaceHelper(s, i) ==> s[j] != ' '
  decreases |s| - i
{
  if i == |s| then i
  else if s[i] == ' ' then i
  else FindSpaceHelper(s, i + 1)
}

datatype Risk = Low | Medium | High

datatype RuntimeDataState = RuntimeDataState(
  name: string,
  request: string,
  risk: Risk,
  AI_used: bool,
  AI_input: string,
  human_used: bool,
  response: string
)

const offensiveWords: seq<string>

}