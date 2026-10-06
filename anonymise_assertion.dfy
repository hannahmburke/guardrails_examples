include "helpdesk-utils.dfy"

module main{
  import opened U = Utils

  // Predicate: word containment
  predicate Contains(input: string, banned: string)
  {
    var words := Split(input);
    banned in words
  }

  // Lemma that shows all elements resulting from Split have no spaces
  lemma SplitNoSpaces(s: string)
    ensures forall i :: 0 <= i < |Split(s)| ==> NoSpaces(Split(s)[i])
    decreases |s|
  {
    var idx := FindSpace(s);
    if idx == |s| {
    } else {
      SplitNoSpaces(s[idx+1..]);
    }
  }

  // Predicate: no spaces in string
  predicate NoSpaces(s: string)
  {
    forall i :: 0 <= i < |s| ==> s[i] != ' '
  }

  // Join sequence of words with spaces inbetween
  function Join(words: seq<string>): string
  {
    if |words| == 0 then ""
    else if |words| == 1 then words[0]
    else words[0] + " " + Join(words[1..])
  }

  // Lemma that Split and Join are inverse functions
  lemma SplitJoinInverse(words: seq<string>)
    requires forall i :: 0 <= i < |words| ==> NoSpaces(words[i])
    requires |words|>0
    ensures Split(Join(words)) == words
    decreases |words|
  {
    if |words| == 0 {
    } else if |words| == 1 {
      var idx := FindSpace(words[0]);
      assert idx == |words[0]|;
    } else {
      assert Join(words)[|words[0]|] == ' ';
      var idx := FindSpace(Join(words));
      assert idx == |words[0]|;
      assert Join(words)[..idx] == words[0];
      assert Join(words)[idx+1..] == Join(words[1..]);
      SplitJoinInverse(words[1..]);
    }
  }


  // Replace all occurrences of `name` in `input` with `pseudonym`
  method ReplaceAll(request: string, name: string, pseudonym: string) returns (AI_input: string)
  requires pseudonym!=name
  requires NoSpaces(pseudonym)
  ensures !Contains(AI_input, name)
  {
    var words := Split(request);
    assert |words|>0;
    SplitNoSpaces(request);
    assert forall i :: 0 <= i < |words| ==> NoSpaces(words[i]);

    var i := 0;

    var replacedWords := [];

    while i < |words|
      invariant 0 <= i <= |words|
      invariant |replacedWords| == i
      invariant !(name in replacedWords)
      invariant forall k :: 0 <= k < |replacedWords| ==> NoSpaces(replacedWords[k])
    {
      var word := if words[i] == name then pseudonym else words[i];
      assert word != name;
      assert NoSpaces(word);

      replacedWords := replacedWords + [word];

      i := i + 1;
    }
    AI_input := Join(replacedWords);
    assert |replacedWords|>0;
    assert forall i :: 0 <= i < |replacedWords| ==> NoSpaces(replacedWords[i]);


    SplitJoinInverse(replacedWords);
    assert Split(AI_input) == replacedWords;
    assert name !in replacedWords;
    assert name !in Split(AI_input);
    
  }

  // Method representing the anonymisation task
  method AnonymiseRequest(d_q: RuntimeDataState)
    returns (d_q1: RuntimeDataState)

    // inputAnonymised assertion
    ensures !Contains(d_q1.AI_input, d_q1.name)

    // unchanged edge assertions between d_q and d_q1:
    // AI_used
    ensures d_q1.AI_used == d_q.AI_used 
    //human_used
    ensures d_q1.human_used == d_q.human_used 
    //highRisk
    ensures (d_q1.risk == High) == (d_q.risk == High) 
    // noOffensiveTerms
    ensures ((Intersection(offensiveWords,Split(d_q1.response)) == {}) == (Intersection(offensiveWords,Split(d_q.response)) == {} )) 
    
  {
      // Choose a pseudonym that is different to name
      var pseudonym := if "anonymous" == d_q.name then "pseudonym" else "anonymous";
      var anonRequest := ReplaceAll(d_q.request, d_q.name, pseudonym);
      d_q1 := RuntimeDataState(
        d_q.name,
        d_q.request,
        d_q.risk,
        d_q.AI_used,
        anonRequest,
        d_q.human_used,
        d_q.response
      );
  }
}