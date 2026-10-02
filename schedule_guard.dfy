// ---------- Types ----------
type Resource(==)

datatype Job = Job(
  start: int,
  end: int,
  resources: map<Resource,int>
)

datatype JobInfo = JobInfo(
  duration: int,
  resources: set<Resource>
)


// ---------- Helper functions ----------

// Recursive definition of makespan
function makespan(S: seq<Job>): int
{
  if |S| == 0 then 0
  else if |S| == 1 then S[0].end
  else if S[0].end > makespan(S[1..]) then S[0].end
  else makespan(S[1..])
}

// Resource usage at a given job start time
function resourceUsage(o: seq<Job>, j: int, r: Resource): int
  requires 0 <= j < |o|
{
  if |o| == 0 then 0
  else
    resourceUsageRec(o, j, r, 0)
}

function resourceUsageRec(o: seq<Job>, j: int, r: Resource, x: int): int
  requires 0 <= j < |o|
  requires 0 <= x <= |o|
  decreases |o| - x
{
  if x == |o| then 0
  else
    (if o[j].start >= o[x].start &&
        o[j].start < o[x].end &&
        r in o[x].resources
     then o[x].resources[r]
     else 0)
    + resourceUsageRec(o, j, r, x + 1)
}

// Detects whether any capacity increased
function increasedCapacity(Cnew: map<Resource,int>, Cold: map<Resource,int>): bool
{
    if exists r ::
    r in Cnew && r in Cold && Cnew[r] > Cold[r] then true
    else false
}



// ---------- Input predicates (I_v) ----------

// Schedule is executable under capacity C
predicate isExecutable(S: seq<Job>, J: seq<JobInfo>, C: map<Resource,int>)
{
  |J| == |S| &&
  forall j :: 0 <= j < |S| ==>
    forall r ::
      r in J[j].resources ==>
        r in C &&
        resourceUsage(S, j, r) <= C[r]
}

// Durations preserved
predicate durPreserved(S: seq<Job>, J: seq<JobInfo>)
{
  |J| == |S| &&
  forall j :: 0 <= j < |S| ==>
    S[j].end - S[j].start == J[j].duration
}

// Initial schedule is executable
predicate initExecutable(i: seq<Job>, J: seq<JobInfo>, C: map<Resource,int>) //REF: line_initExDef
{
  isExecutable(i, J, C)
}

// Initial schedule is optimal
ghost predicate initOptimised(i: seq<Job>, J: seq<JobInfo>, Cold: map<Resource,int>) //REF: line_initOpDef
{
  !exists S: seq<Job> ::
    makespan(S) < makespan(i)
    &&
    durPreserved(S, J)
    &&
    isExecutable(S, J, Cold)
}

// Relevant resources must be defined in both maps
predicate JobResourcesCovered(J: seq<JobInfo>, Cold: map<Resource,int>, Cnew: map<Resource,int>)
{
  forall j, r ::
    0 <= j < |J| && r in J[j].resources ==>
      r in Cold && r in Cnew
}


// ---------- Key lemma ----------
lemma FasterWithoutIncreaseImpliesInvalid(
  i: seq<Job>,
  o: seq<Job>,
  J: seq<JobInfo>,
  Cold: map<Resource,int>,
  Cnew: map<Resource,int>
)
  requires initOptimised(i, J, Cold)
  requires !increasedCapacity(Cnew, Cold)
  requires makespan(o) < makespan(i)
  requires JobResourcesCovered(J, Cold, Cnew)
  ensures !durPreserved(o, J) || !isExecutable(o, J, Cnew)
{
  // Instantiate optimality with S = o
  assert !(
    makespan(o) < makespan(i) &&
    durPreserved(o, J) &&
    isExecutable(o, J, Cold)
  ); //REF: line_lemma-inst

  // Split conjunction
  assert !durPreserved(o, J) ||
         !isExecutable(o, J, Cold); //REF: line_lemma-split

  // Coverage of relevant resources
  assert forall j, r ::
    0 <= j < |J| && r in J[j].resources ==>
      r in Cold && r in Cnew;

  // Capacity does not increase
  assert forall r ::
    r in Cnew && r in Cold ==> Cnew[r] <= Cold[r];

  if !durPreserved(o, J) {
  } else {
    assert !isExecutable(o, J, Cold);
    // Monotonicity step
    assert !isExecutable(o, J, Cnew); //REF: line_lemma-monotone
  }
}


// ---------- Constraint ----------
predicate Constraint(
  o: seq<Job>,
  J: seq<JobInfo>,
  C: map<Resource,int>,
  deadline: int
)
{
  durPreserved(o, J)
  &&
  isExecutable(o, J, C)
  &&
  makespan(o) <= deadline
}


datatype RuntimeDataState = RuntimeDataState(
  J: seq<JobInfo>,
  Cold: map<Resource,int>,
  C: map<Resource,int>,
  init: seq<Job>,
  deadline: int,
  final: seq<Job>
)

// ---------- Guard ----------
method guardEval(
    d_in: RuntimeDataState,
    d_out: RuntimeDataState 
) returns (result: bool)

  requires !initExecutable(d_in.init, d_in.J, d_in.C) //REF: line_executability-pred
  requires initOptimised(d_in.init, d_in.J, d_in.Cold) //REF: line_optimality-pred
  requires JobResourcesCovered(d_in.J, d_in.Cold, d_in.C)

  ensures result <==> Constraint(d_out.final, d_in.J, d_in.C, d_in.deadline) //REF: line_guard-constraints
{
  // Early exit: unchanged schedule
  if d_out.final == d_in.init {
    return false; //REF: line_early-same
  }

  // Early exit using optimality argument
  if !increasedCapacity(d_in.C, d_in.Cold) && //REF: line_increased-cap
    makespan(d_out.final) < makespan(d_in.init) {
    FasterWithoutIncreaseImpliesInvalid(d_in.init, d_out.final, d_in.J, d_in.Cold, d_in.C);
    return false; //REF: line_early-opt
  }

  // Structural consistency
  if |d_in.J| != |d_out.final| {return false;} //REF: line_length-check

  // Duration preservation
  var j := 0;
  while j < |d_out.final|
    invariant 0 <= j <= |d_out.final|
    invariant forall k :: 0 <= k < j ==> //REF: line_preservation
      d_out.final[k].end - d_out.final[k].start == d_in.J[k].duration 
  {
    if d_out.final[j].end - d_out.final[j].start != d_in.J[j].duration {
      return false;
    }
    j := j + 1;
  }

  // Executability
  var j2 := 0;
  while j2 < |d_out.final|
    invariant 0 <= j2 <= |d_out.final|
    invariant forall k :: 0 <= k < j2 ==>
      forall r :: r in d_in.J[k].resources ==>
        resourceUsage(d_out.final, k, r) <= d_in.C[r]
  {
    var rset := d_in.J[j2].resources;

    if exists r ::
         r in rset &&
         resourceUsage(d_out.final, j2, r) > d_in.C[r]
    {
      return false; //REF: line_resource
    }

    j2 := j2 + 1;
  }

  // Deadline constraint
  if makespan(d_out.final) > d_in.deadline {
    return false; //REF: line_deadline
  }

  return true; //REF: line_success
}