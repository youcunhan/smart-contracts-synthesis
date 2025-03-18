# 1. Datalog without validation guards (for synthesis input) - Keeping core logic intact
datalog_synthesis_input = """
// Parameters
.decl *totalSupply(n: uint)
.decl *buyTaxPercent(n: uint)
.decl *sellTaxPercent(n: uint)
.decl *tradeVolume(n: uint)
.decl balanceOf(p: address, n: uint)[0]
.decl constructor(n: uint)

// Transactions
.decl buyTokens(p: address, amount: uint)
.decl sellTokens(p: address, amount: uint)
.decl claimDevTax(p: address, amount: uint)
.decl claimCommunityTax(p: address, amount: uint)
.decl claimDevToken(p: address, amount: uint)

// Rules
totalSupply(n) :- constructor(n).
buyTokens(p, n) :- balanceOf(p, m), m >= n.
sellTokens(p, n) :- balanceOf(p, m), m >= n.
claimDevTax(p, n) :- balanceOf(p, m), m >= n.
claimCommunityTax(p, n) :- balanceOf(p, m), m >= n.
claimDevToken(p, n) :- balanceOf(p, m), m >= n.

.decl *totalTraded(n: uint)
totalTraded(n) :- n = sum t: tradeVolume(t).
"""

# 2. Example traces for synthesis (at least 3 traces)
example_traces = """
// Trace 1: Buying tokens
buyTokens(p=0x123456, amount=500)@1;
sellTokens(p=0x123456, amount=200)@2;
claimCommunityTax(p=0x123456, amount=50)@3;

// Trace 2: Selling and claiming dev tokens
buyTokens(p=0xabcdef, amount=1000)@1;
sellTokens(p=0xabcdef, amount=500)@2;
claimDevToken(p=0xabcdef, amount=100)@3;

// Trace 3: Buying, claiming taxes, and trading volume increase
buyTokens(p=0x112233, amount=2000)@1;
claimDevTax(p=0x112233, amount=150)@2;
sellTokens(p=0x112233, amount=1800)@3;
"""

# 3. Properties for BMC (to find counterexamples)
safety_properties = """
// Ensuring total supply remains constant
□(totalSupply(n) → n = constructor(n))

// Ensuring total traded volume is calculated correctly
□(totalTraded(n) → n = sum t: tradeVolume(t))

// Ensuring no negative balance for any account
□(balanceOf(p, n) → n ≥ 0)

// Ensuring tax claims do not exceed balance
□(claimDevTax(p, a) → balanceOf(p, m) ∧ m ≥ a)
□(claimCommunityTax(p, a) → balanceOf(p, m) ∧ m ≥ a)
□(claimDevToken(p, a) → balanceOf(p, m) ∧ m ≥ a)
"""

import os
# Defining file paths
output_dir = "./synthesis-benchmark/sss/"
datalog_file = output_dir + "sss.dl"
example_traces_file = output_dir + "example_traces.txt"
temporal_properties_file = output_dir + "temporal_properties.txt"

# Ensure the directory exists
os.makedirs(output_dir, exist_ok=True)

# Writing files
with open(datalog_file, "w") as f:
    f.write(datalog_synthesis_input)

with open(example_traces_file, "w") as f:
    f.write(example_traces)

with open(temporal_properties_file, "w") as f:
    f.write(safety_properties)

# Confirming file creation
[datalog_file, example_traces_file, temporal_properties_file]
