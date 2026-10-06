# Running Examples

This repository contains the Dafny and NuXmv files associated with the paper:

> **Guaranteeing Compliance of AI Systems Through Formal Verification of Runtime Guardrails**

The examples demonstrate how guard correctness and system-level compliance can be formally verified. 

---

# Example 1: User Helpdesk

## Dafny Verification

### Shared Utilities

**File:** `helpdesk-utils.dfy`

Contains reusable string-processing functions, as well as the RuntimeDataState definition

### Guard Verification

**File:** `offensive_guard.dfy`

Verifies that the guard returns `true` if and only if the AI-generated response contains no offensive words.

### Edge Assertion Verification

**File:** `anonymisation_assertion.dfy`

Verifies that the *Anonymise Request* action results in the `inputAnonymised` edge assertion:

```text
!AI_input.contains(name)
```
and verifies the action preserves the state of the other edge assertions:

- `noOffensiveTerms`
- `highRisk`
- `AI_used`
- `human_used`


---

## NuXmv Verification

### Kripke Structure and LTL Properties
**File:** `user-helpdesk.smv`

The Kripke structure defines the control flow between states, beginning at `input` and progressing through risk assessment, anonymisation, AI processing, and possible human intervention. The branching behaviour based on risk is encoded in the transitions at line 46.
Assertion updates are specified explicitly and updated after the appropriate states. For instance, *inputAnonymised* is set to `true` at the `anonymise` state (line 50), while *noOffensiveWords* is reset at the `ai` state (line 96).
As seen in the control-flow cases within the `guard_eval` state (line 57), outputs produced by the AI are only allowed to proceed to un-anonymising if no offensive content is detected. Otherwise, they are escalated to human review.

The requirements are encoded as LTL specifications at the end of the file, ensuring that:

1. AI is only applied to anonymised inputs.
2. AI outputs are either safe or subject to human review before being sent.
3. All high-risk inputs necessarily involve human processing.

### Model Checking commands
**File:** `ic3_cmd.smv`

Contains the commands required to run the IC3 model checking algorithm and verify that all LTL specifications in `user-helpdesk.smv` hold.

---

# Example 2: Schedule Adjustment System 

## Dafny Verification

### Guard Verification
**File:** `schedule_guard.dfy`

Verifies that the guard returns `true` if and only if the AI-generated schedule satisfies the required schedule validity conditions.

---

## NuXmv Verification

### Kripke Structure and LTL Properties
**File:** `schedule-adjustment.smv`

The process model is converted to a Kripke structure, dictating the control-flow between states of the model, and how edge assertions are affected at each state.
As seen in lines 175, 186 and 199, the validity conditions for the output AI schedule become `unknown`, but through the guard in line 115, the AI schedule does not reach implementation unless the required assertions are met. All other control-flow elements are also incorporated, in particular the capped number of retries, as seen in line 126.

The two requirements are written on lines 226 and 229 as LTL specifications in terms of the edge assertions.

### AI Input Restrictions

For the AI input restrictions, we firstly check which paths are present. This can also be done using LTL specifications, where each specification represents a distinct path, but is written such that the path does not exist.
In this case (besides the loop), each state leading to the AI component represents a distinct separate path. That is, the AI component can be reached from:

- (a) **Executable with Delays?** returns *No*.
- (b) **Delayed Schedule Meets Deadline?** returns *No*.
- (c) **>10 Attempts?** returns *No*.

For each path, we write the specification such that the preceding state never occurs, as seen in lines 242 to 247.

In this case all paths should lead to the same input restrictions:

```text
initExecutable = false
initOptimised  = true
```

These restrictions are verified by an LTL property on line 253 that checks that the assertions always hold whenever execution reaches the AI component.

### IC3 Verification Commands
**File:** `ic3_cmd.smv`

Contains the commands required to run the IC3 model checking algorithm.

The verification confirms:

- All compliance requirement LTL specifications hold.
- All path-existence checks produce counterexamples, demonstrating that each of the three paths to the AI action is reachable.
- The AI input restrictition LTL specification holds

The IC3 algorithm is well suited to this example because it can reason about the looping process model without requiring an explicit bound on the number of loop iterations.

---

# Repository Structure

```text
helpdesk-utils.dfy
offensive_guard.dfy
anonymisation_assertion.dfy
user-helpdesk.smv
schedule_guard.dfy
schedule-adjustment.smv
ic3_cmd.smv
```

---

# Reproducing the Results

## Example 1: User Helpdesk

### Verify Guard Correctness Using Dafny

```bash
dafny verify offensive_guard.dfy
```

### Verify Edge Assertion Using Dafny
```bash
dafny verify anonymisation_assertion.dfy
```

### Verify Process-Level Requirements Using NuXmv

```bash
nuXmv -source ic3_cmd.smv user-helpdesk.smv
```

---

## Example 2: Schedule Adjustment System

### Verify Guard Correctness Using Dafny

```bash
dafny verify schedule_guard.dfy
```

### Verify Process-Level Requirements Using NuXmv

```bash
nuXmv -source ic3_cmd.smv schedule-adjustment.smv
```