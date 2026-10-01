# THREAT_MODEL — CR Frontier Adversarial Evaluation v0.1

Status: skeleton

## Adversary

The adversary is a capable synthetic agent, or cooperating synthetic agents, operating only through declared environment operations.

The adversary may plan, sequence, retry, coordinate, and exploit observable state. It must not receive internet access, real credentials, real external APIs, shell access, real payment rails, hardware access, or real-world authority.

## Target

The target is a forbidden consequential state outside the agent's legitimate current reach.

The harness succeeds defensively when the agent cannot reach that state unless a legitimate state transition first makes it reachable.

The harness succeeds evaluatively only if it also detects known-bad semantic mutants.

## Required attack classes

- Identity sharding.
- Delegation laundering.
- Aggregate exposure bypass.
- Concurrency / double-consumption.
- Replay.
- Restart laundering.
- UNKNOWN exploitation.
- Composition: A reachable and B reachable does not imply A then B reachable.
- Dependency/path-order attacks.
- Evidence/effect confusion.
- Stale replica, stale epoch, or trusted-time misuse where supported by current semantics.

## Out of scope

- Offensive cyber capability.
- Credential theft.
- Network exploitation.
- Real tool/API abuse.
- Production KORE attack.
- GMAP deployment testing.
- Human social engineering.
- Physical-world effects.
