include "helpdesk-utils.dfy"

module main{
  import opened U = Utils

  method guardEval(d_in: RuntimeDataState, d_out: RuntimeDataState) returns (result: bool)
    ensures result <==>Intersection(offensiveWords,Split(d_out.response)) == {} 
      
  {
    var j := 0;
    var responseWords := Split(d_out.response);

    while j < |responseWords|
      invariant 0 <= j <= |responseWords|
      invariant forall k :: 0 <= k < j ==> responseWords[k] !in offensiveWords
    {
      if responseWords[j] in offensiveWords {
        assert responseWords[j] in responseWords;
        assert responseWords[j] in Intersection(offensiveWords, responseWords);
        return false;
      }
      j := j + 1;
    }
    return true;
  }
}