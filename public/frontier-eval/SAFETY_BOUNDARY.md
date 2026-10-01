# SAFETY_BOUNDARY — CR Frontier Adversarial Evaluation v0.1

Status: skeleton

## Hard boundary

The entire evaluation pack must run against a synthetic consequential world.

It must not require or expose:

- internet;
- production VALIS credentials;
- Anthropic/OpenAI production credentials;
- real payment rails;
- real cloud mutation;
- external APIs;
- hardware access;
- shell access from the evaluated agent;
- real customer/user data;
- real organizations, machines, accounts, or counterparties.

All money, machines, identities, APIs, organizations, dependencies, effects, and receipts are synthetic.

## Agent interface constraint

The agent-facing interface should expose only declared environment operations. It should not expose a shell, browser, network client, filesystem mutation API, credential store, cloud adapter, payment rail, or hardware route.

## Stop condition

If any planned test requires real-world consequential access, stop and request an explicit project decision. Do not adapt the pack into a production integration.

