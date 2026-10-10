module

/-
Copyright 2026 Linmiao Xu.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

@[expose] public section

/-!
# Erdős Problem 261: Pure-Kernel Certificate Core (No Mathlib Import)

This module contains the pure `Nat`/`Bool`/`List` definitions for the coalesced
dyadic block certificate verifier (`wSpec`, `w64`, `stepVar`, `runB64`, `MergeTree`,
`evalState`, `checkForestStates`, `mergeSorted`, `treeToLists`, `forestToLists`,
`mergeListPairs`, `mergeAllLists`, `checkSeq`). Because it does not import `Mathlib`,
certificate data modules importing only `CertificateCore261` compile with ~500 MiB
baseline RSS instead of ~6,900 MiB.
-/

namespace Erdos261

/-- Bit-by-bit specification of the dyadic block weight $W_b(M) = \sum_{j=0}^{b-1} j \cdot \varepsilon_j 2^{b-1-j}$
for a $b$-step inclusion mask $M < 2^b$. -/
def wSpec : Nat → Nat → Nat
  | 0, _ => 0
  | b + 1, M => 2 * wSpec b (M / 2) + b * (M % 2)

def w8Swar (M : Nat) : Nat :=
  4 * (M &&& 0x0F) + 2 * (M &&& 0x33) + (M &&& 0x55)

def w16Swar (M : Nat) : Nat :=
  8 * (M &&& 0x00FF) + 4 * (M &&& 0x0F0F) + 2 * (M &&& 0x3333) + (M &&& 0x5555)

def w32Swar (M : Nat) : Nat :=
  16 * (M &&& 0x0000FFFF) + 8 * (M &&& 0x00FF00FF) +
   4 * (M &&& 0x0F0F0F0F) + 2 * (M &&& 0x33333333) + (M &&& 0x55555555)

/-- 64-bit SWAR evaluation of $W_{64}(M)$. -/
def w64 (M : Nat) : Nat :=
  32 * (M &&& 0x00000000FFFFFFFF) +
  16 * (M &&& 0x0000FFFF0000FFFF) +
   8 * (M &&& 0x00FF00FF00FF00FF) +
   4 * (M &&& 0x0F0F0F0F0F0F0F0F) +
   2 * (M &&& 0x3333333333333333) +
   1 * (M &&& 0x5555555555555555)

def checkW8 : Nat → Bool
  | 0 => true
  | m + 1 => (w8Swar m == wSpec 8 m) && checkW8 m

theorem checkW8_256 : checkW8 256 = true := by decide +kernel

/-- Single-shot variable-length block transition for $0 \le b \le 64$ using shifted `w64`. -/
def stepVar (b M i v : Nat) : Option (Nat × Nat) :=
  if b == 0 then some (i, v)
  else if b ≤ 64 && M < (1 <<< b) then
    let sh := 64 - b
    let w := (w64 (M <<< sh)) >>> sh
    let sub := i * M + w
    let vb := v <<< b
    if sub < vb then some (i + b, vb - sub) else none
  else none

/-- Multi-block 64-step transition followed by a variable-length remainder block. -/
def runB64 : List Nat → Nat → Nat → Nat → Nat → Option (Nat × Nat)
  | [], b, M, i, v => stepVar b M i v
  | M64 :: ms, b, M, i, v =>
    match stepVar 64 M64 i v with
    | some (i', v') => runB64 ms b M i' v'
    | none => none

inductive MergeTree where
  | leaf (n : Nat) (b64 : List Nat) (b : Nat) (M : Nat) : MergeTree
  | merge (left right : MergeTree) (b64 : List Nat) (b : Nat) (M : Nat) : MergeTree

def evalState : MergeTree → Option (Nat × Nat)
  | .leaf n b64 b M =>
    if 2 ≤ n then runB64 b64 b M (n + 2) (n - 1) else none
  | .merge l r b64 b M =>
    match evalState l, evalState r with
    | some (i1, v1), some (i2, v2) =>
      if i1 == i2 && v1 == v2 then runB64 b64 b M i1 v1 else none
    | _, _ => none

def treeToLists : MergeTree → List (List Nat) → List (List Nat)
  | .leaf n _ _ _, acc => if 2 ≤ n then [n] :: acc else acc
  | .merge l r _ _ _, acc => treeToLists l (treeToLists r acc)

def forestToLists : List MergeTree → List (List Nat) → List (List Nat)
  | [], acc => acc
  | t :: ts, acc => treeToLists t (forestToLists ts acc)

def checkForestStates : List MergeTree → Bool
  | [] => true
  | t :: ts =>
    match evalState t with
    | some (i, v) => (2 * v == i) && checkForestStates ts
    | none => false

def mergeSorted : Nat → List Nat → List Nat → List Nat
  | 0, xs, _ => xs
  | _, [], ys => ys
  | _, xs, [] => xs
  | fuel + 1, x :: xs, y :: ys =>
    if x ≤ y then x :: mergeSorted fuel xs (y :: ys)
    else y :: mergeSorted fuel (x :: xs) ys

def mergeListPairs : Nat → List (List Nat) → List (List Nat)
  | fuel, l1 :: l2 :: ls => mergeSorted fuel l1 l2 :: mergeListPairs fuel ls
  | _, ls => ls

def mergeAllLists : Nat → Nat → List (List Nat) → List Nat
  | 0, _, l :: _ => l
  | _, _, [] => []
  | _, _, [l] => l
  | d + 1, w, ls => mergeAllLists d (2 * w) (mergeListPairs (2 * w) ls)

def checkSeq : Nat → Nat → List Nat → Bool
  | _, 0, _ => true
  | _, _ + 1, [] => false
  | n, c + 1, m :: ms => (m == n) && checkSeq (n + 1) c ms

end Erdos261
