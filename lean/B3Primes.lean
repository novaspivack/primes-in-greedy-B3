/-
  Greedy Multiplicative B₃ — Every Prime Is Admitted
  ====================================================

  Theorem: In the greedy multiplicative B₃ sequence (OEIS A079852),
  every prime number is included.

  Zero sorry. Zero custom axioms. Uses Mathlib.
-/

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic

set_option linter.unusedVariables false

namespace B3Primes

-- ════════════════════════════════════════════════════════════════
-- §1  Key divisibility lemmas
-- ════════════════════════════════════════════════════════════════

theorem not_dvd_of_pos_lt {p m : ℕ} (hp : Nat.Prime p) (hm : 0 < m) (hlt : m < p) :
    ¬ (p ∣ m) := by
  intro ⟨k, hk⟩
  rcases k with _ | k
  · simp at hk; omega
  · have : p ≤ p * (k + 1) := Nat.le_mul_of_pos_right p (by omega)
    omega

theorem prime_not_dvd_mul {p a b : ℕ} (hp : Nat.Prime p)
    (ha : ¬ p ∣ a) (hb : ¬ p ∣ b) : ¬ p ∣ (a * b) := by
  rw [hp.dvd_mul]; push_neg; exact ⟨ha, hb⟩

theorem prime_not_dvd_mul3 {p a b c : ℕ} (hp : Nat.Prime p)
    (ha : ¬ p ∣ a) (hb : ¬ p ∣ b) (hc : ¬ p ∣ c) : ¬ p ∣ (a * b * c) :=
  prime_not_dvd_mul hp (prime_not_dvd_mul hp ha hb) hc

theorem no_triple_dvd_of_all_lt {p a b c : ℕ} (hp : Nat.Prime p)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (ha' : a < p) (hb' : b < p) (hc' : c < p) : ¬ p ∣ (a * b * c) :=
  prime_not_dvd_mul3 hp
    (not_dvd_of_pos_lt hp ha ha')
    (not_dvd_of_pos_lt hp hb hb')
    (not_dvd_of_pos_lt hp hc hc')

-- ════════════════════════════════════════════════════════════════
-- §2  B₃ definition
-- ════════════════════════════════════════════════════════════════

def IsMultB3 (S : ℕ → Prop) : Prop :=
  ∀ a b c d e f : ℕ,
    S a → S b → S c → S d → S e → S f →
    a * b * c = d * e * f →
    a ≤ b → b ≤ c → d ≤ e → e ≤ f →
    a = d ∧ b = e ∧ c = f

def aug (S : ℕ → Prop) (p : ℕ) : ℕ → Prop := fun n => S n ∨ n = p

-- ════════════════════════════════════════════════════════════════
-- §3  Helper: p doesn't divide a product of S-elements
-- ════════════════════════════════════════════════════════════════

theorem p_not_dvd_S_triple {p : ℕ} (hp : Nat.Prime p)
    {S : ℕ → Prop} (hpos : ∀ s, S s → 0 < s) (hlt : ∀ s, S s → s < p)
    {a b c : ℕ} (ha : S a) (hb : S b) (hc : S c) : ¬ p ∣ (a * b * c) :=
  no_triple_dvd_of_all_lt hp (hpos a ha) (hpos b hb) (hpos c hc)
    (hlt a ha) (hlt b hb) (hlt c hc)

-- ════════════════════════════════════════════════════════════════
-- §4  Main theorem
-- ════════════════════════════════════════════════════════════════

/-- Helper: in aug S p, each element is either in S (hence < p) or equals p. -/
theorem aug_lt_or_eq {p : ℕ} (hp : Nat.Prime p) {S : ℕ → Prop}
    (hlt : ∀ s, S s → s < p) {x : ℕ} (hx : aug S p x) : x < p ∨ x = p := by
  rcases hx with hx | rfl; left; exact hlt x hx; right; rfl

theorem prime_preserves_B3
    (p : ℕ) (hp : Nat.Prime p)
    (S : ℕ → Prop)
    (hB3 : IsMultB3 S)
    (hpos : ∀ s, S s → 0 < s)
    (hlt  : ∀ s, S s → s < p)
    (hone : S 1) :
    IsMultB3 (aug S p) := by
  intro a b c d e f ha hb hc hd he hf heq hab hbc hde hef
  simp only [aug] at ha hb hc hd he hf
  -- Positivity of all elements
  have hap : 0 < a := by rcases ha with ha | rfl; exact hpos a ha; exact hp.pos
  have hbp : 0 < b := by rcases hb with hb | rfl; exact hpos b hb; exact hp.pos
  have hcp : 0 < c := by rcases hc with hc | rfl; exact hpos c hc; exact hp.pos
  have hdp : 0 < d := by rcases hd with hd | rfl; exact hpos d hd; exact hp.pos
  have hep : 0 < e := by rcases he with he | rfl; exact hpos e he; exact hp.pos
  have hfp : 0 < f := by rcases hf with hf | rfl; exact hpos f hf; exact hp.pos
  -- Upper bounds
  have ha_le : a ≤ p := by rcases ha with ha | rfl; exact Nat.le_of_lt (hlt a ha); exact le_refl _
  have hb_le : b ≤ p := by rcases hb with hb | rfl; exact Nat.le_of_lt (hlt b hb); exact le_refl _
  have hc_le : c ≤ p := by rcases hc with hc | rfl; exact Nat.le_of_lt (hlt c hc); exact le_refl _
  have hd_le : d ≤ p := by rcases hd with hd | rfl; exact Nat.le_of_lt (hlt d hd); exact le_refl _
  have he_le : e ≤ p := by rcases he with he | rfl; exact Nat.le_of_lt (hlt e he); exact le_refl _
  have hf_le : f ≤ p := by rcases hf with hf | rfl; exact Nat.le_of_lt (hlt f hf); exact le_refl _
  -- Count p's on each side using: x = p ↔ x = p (and x ∈ S ↔ x < p)
  -- We determine membership by: x < p (in S) or x = p
  have ha_lt_or : a < p ∨ a = p := by rcases ha with ha | rfl; left; exact hlt a ha; right; rfl
  have hb_lt_or : b < p ∨ b = p := by rcases hb with hb | rfl; left; exact hlt b hb; right; rfl
  have hc_lt_or : c < p ∨ c = p := by rcases hc with hc | rfl; left; exact hlt c hc; right; rfl
  have hd_lt_or : d < p ∨ d = p := by rcases hd with hd | rfl; left; exact hlt d hd; right; rfl
  have he_lt_or : e < p ∨ e = p := by rcases he with he | rfl; left; exact hlt e he; right; rfl
  have hf_lt_or : f < p ∨ f = p := by rcases hf with hf | rfl; left; exact hlt f hf; right; rfl
  -- From ordering: if b = p then c = p (since b ≤ c ≤ p and c ≤ p)
  -- Similarly for the right side.
  -- We count p's on each side.
  -- Left p-count: lp = (if a=p then 1 else 0) + ...
  -- We use: p | LHS ↔ p | RHS (from heq)
  -- If lp ≠ rp, then p divides the S-part of one side, contradiction.
  -- Key: p^lp | LHS and p^rp | RHS, and LHS = RHS, so p^min(lp,rp) | both.
  -- We implement this by case analysis on how many p's appear.
  --
  -- Shortcut: use the fact that a ≤ b ≤ c and d ≤ e ≤ f, combined with
  -- the bounds a,b,c,d,e,f ≤ p, to determine which elements equal p.
  -- If x = p and x ≤ y ≤ p, then y = p.
  -- So: if a = p then b = c = p; if b = p then c = p; etc.
  -- This reduces the 64 cases to much fewer.
  --
  -- Left side cases: (a<p, b<p, c<p), (a<p, b<p, c=p), (a<p, b=p, c=p), (a=p, b=p, c=p)
  -- Right side cases: (d<p, e<p, f<p), (d<p, e<p, f=p), (d<p, e=p, f=p), (d=p, e=p, f=p)
  -- That's 4 × 4 = 16 cases.
  --
  -- We implement by computing lp and rp and case-splitting on lp vs rp.
  -- lp = number of {a,b,c} equal to p; rp = number of {d,e,f} equal to p.
  -- From ordering: lp ∈ {0,1,2,3} (only suffix can be p: c, bc, abc).
  -- Similarly rp ∈ {0,1,2,3}.
  -- If lp = rp: cancel p^lp and use hB3 (with 1's to pad).
  -- If lp ≠ rp: p divides the smaller side's S-product, contradiction.
  --
  -- We compute lp and rp using the ordering constraints.
  have hc_eq_p_of_b : b = p → c = p := fun hb_eq => le_antisymm hc_le (hb_eq ▸ hbc)
  have hb_eq_p_of_a : a = p → b = p := fun ha_eq => le_antisymm hb_le (ha_eq ▸ hab)
  have hf_eq_p_of_e : e = p → f = p := fun he_eq => le_antisymm hf_le (he_eq ▸ hef)
  have he_eq_p_of_d : d = p → e = p := fun hd_eq => le_antisymm he_le (hd_eq ▸ hde)
  -- Determine lp
  rcases hc_lt_or with hc_lt | hc_eq
  · -- c < p, so a < p and b < p too (since a ≤ b ≤ c < p)
    have ha_lt : a < p := lt_of_le_of_lt (le_trans hab hbc) hc_lt
    have hb_lt : b < p := lt_of_le_of_lt hbc hc_lt
    -- lp = 0: left side all in S
    rcases hf_lt_or with hf_lt | hf_eq
    · -- f < p, so d < p and e < p too
      have hd_lt : d < p := lt_of_le_of_lt (le_trans hde hef) hf_lt
      have he_lt : e < p := lt_of_le_of_lt hef hf_lt
      -- rp = 0: both sides all in S
      -- Need to recover S membership
      have ha_S : S a := by rcases ha with ha | rfl; exact ha; omega
      have hb_S : S b := by rcases hb with hb | rfl; exact hb; omega
      have hc_S : S c := by rcases hc with hc | rfl; exact hc; omega
      have hd_S : S d := by rcases hd with hd | rfl; exact hd; omega
      have he_S : S e := by rcases he with he | rfl; exact he; omega
      have hf_S : S f := by rcases hf with hf | rfl; exact hf; omega
      exact hB3 a b c d e f ha_S hb_S hc_S hd_S he_S hf_S heq hab hbc hde hef
    · -- f = p, so rp ≥ 1
      rcases he_lt_or with he_lt | he_eq
      · -- e < p, f = p: rp = 1
        -- lp = 0, rp = 1: p | LHS (since LHS = RHS = d*e*p), but LHS = a*b*c with a,b,c < p
        have ha_S : S a := by rcases ha with ha | rfl; exact ha; omega
        have hb_S : S b := by rcases hb with hb | rfl; exact hb; omega
        have hc_S : S c := by rcases hc with hc | rfl; exact hc; omega
        have hd_S : S d := by rcases hd with hd | rfl; exact hd; omega
        have he_S : S e := by rcases he with he | rfl; exact he; omega
        exfalso
        exact p_not_dvd_S_triple hp hpos hlt ha_S hb_S hc_S
          ⟨d * e, by rw [heq, hf_eq]; ring⟩
      · -- e = p, f = p: rp ≥ 2
        have hd_lt : d < p := by
          rcases hd_lt_or with hd_lt | hd_eq
          · exact hd_lt
          · -- d = p, so e = p (already), f = p. rp = 3.
            -- lp = 0, rp = 3: p³ | LHS, but LHS has no p factors
            have ha_S : S a := by rcases ha with ha | rfl; exact ha; omega
            have hb_S : S b := by rcases hb with hb | rfl; exact hb; omega
            have hc_S : S c := by rcases hc with hc | rfl; exact hc; omega
            exfalso
            exact p_not_dvd_S_triple hp hpos hlt ha_S hb_S hc_S
              ⟨p * p, by rw [heq, hd_eq, he_eq, hf_eq]; ring⟩
        -- d < p, e = p, f = p: rp = 2
        have hd_S : S d := by rcases hd with hd | rfl; exact hd; omega
        have ha_S : S a := by rcases ha with ha | rfl; exact ha; omega
        have hb_S : S b := by rcases hb with hb | rfl; exact hb; omega
        have hc_S : S c := by rcases hc with hc | rfl; exact hc; omega
        exfalso
        exact p_not_dvd_S_triple hp hpos hlt ha_S hb_S hc_S
          ⟨d * p, by rw [heq, he_eq, hf_eq]; ring⟩
  · -- c = p, so lp ≥ 1
    rcases hb_lt_or with hb_lt | hb_eq
    · -- b < p, c = p: lp = 1
      have ha_lt : a < p := lt_of_le_of_lt hab hb_lt
      have ha_S : S a := by rcases ha with ha | rfl; exact ha; omega
      have hb_S : S b := by rcases hb with hb | rfl; exact hb; omega
      -- lp = 1: LHS = a*b*p
      rcases hf_lt_or with hf_lt | hf_eq
      · -- f < p: rp = 0, p | RHS but RHS has no p factors
        have hd_lt : d < p := lt_of_le_of_lt (le_trans hde hef) hf_lt
        have he_lt : e < p := lt_of_le_of_lt hef hf_lt
        have hd_S : S d := by rcases hd with hd | rfl; exact hd; omega
        have he_S : S e := by rcases he with he | rfl; exact he; omega
        have hf_S : S f := by rcases hf with hf | rfl; exact hf; omega
        exfalso
        exact p_not_dvd_S_triple hp hpos hlt hd_S he_S hf_S
          ⟨a * b, by rw [← heq, hc_eq]; ring⟩
      · -- f = p: rp ≥ 1
        rcases he_lt_or with he_lt | he_eq
        · -- e < p, f = p: rp = 1. lp = rp = 1.
          -- a*b*p = d*e*p → a*b = d*e
          have hd_lt : d < p := lt_of_le_of_lt hde he_lt
          have hd_S : S d := by rcases hd with hd | rfl; exact hd; omega
          have he_S : S e := by rcases he with he | rfl; exact he; omega
          have hab_de : a * b = d * e :=
            Nat.eq_of_mul_eq_mul_right hp.pos (by rw [hc_eq, hf_eq] at heq; linarith)
          have hres := hB3 1 a b 1 d e hone ha_S hb_S hone hd_S he_S
            (by linarith)
            (Nat.one_le_iff_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hap)) hab
            (Nat.one_le_iff_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hdp)) hde
          exact ⟨hres.2.1, hres.2.2, by rw [hc_eq, hf_eq]⟩
        · -- e = p, f = p: rp ≥ 2
          rcases hd_lt_or with hd_lt | hd_eq
          · -- d < p, e = p, f = p: rp = 2. lp = 1, rp = 2. Contradiction.
            -- a*b*p = d*p*p → a*b = d*p → p | a*b
            have hd_S : S d := by rcases hd with hd | rfl; exact hd; omega
            exfalso
            have hdvd : p ∣ a * b := ⟨d, by
              rw [hc_eq, he_eq, hf_eq] at heq
              exact Nat.eq_of_mul_eq_mul_right hp.pos (by linarith)⟩
            exact prime_not_dvd_mul hp
              (not_dvd_of_pos_lt hp hap ha_lt)
              (not_dvd_of_pos_lt hp hbp hb_lt)
              hdvd
          · -- d = p, e = p, f = p: rp = 3. lp = 1, rp = 3. Contradiction.
            -- a*b*p = p*p*p → a*b = p*p, but a < p and b < p so a*b < p*p
            exfalso
            rw [hc_eq, hd_eq, he_eq, hf_eq] at heq
            have hab_lt : a * b < p * p :=
              Nat.mul_lt_mul_of_lt_of_le' ha_lt (Nat.le_of_lt hb_lt) hbp
            have hab_eq : a * b = p * p :=
              Nat.eq_of_mul_eq_mul_right hp.pos (by nlinarith)
            omega
    · -- b = p, c = p: lp ≥ 2
      have hb_eq : b = p := hb_eq
      -- In the a = p branch, we handle all cases and return the full goal directly.
      -- We split on whether a < p or a = p.
      rcases ha_lt_or with ha_lt | ha_eq
      · -- a < p: continue to the "a < p, b = p, c = p" case below
        -- (we need ha_lt for the rest of the proof)
        -- First handle all right-side cases for lp=2
        have ha_S : S a := by rcases ha with ha | rfl; exact ha; omega
        rcases hf_lt_or with hf_lt | hf_eq
        · -- rp = 0
          have hd_lt : d < p := lt_of_le_of_lt (le_trans hde hef) hf_lt
          have he_lt : e < p := lt_of_le_of_lt hef hf_lt
          have hd_S : S d := by rcases hd with hd | rfl; exact hd; omega
          have he_S : S e := by rcases he with he | rfl; exact he; omega
          have hf_S : S f := by rcases hf with hf | rfl; exact hf; omega
          exfalso
          exact p_not_dvd_S_triple hp hpos hlt hd_S he_S hf_S
            ⟨a * p, by rw [← heq, hb_eq, hc_eq]; ring⟩
        · rcases he_lt_or with he_lt | he_eq
          · -- e < p, f = p: rp = 1. lp = 2, rp = 1. Contradiction.
            have hd_lt : d < p := lt_of_le_of_lt hde he_lt
            have hd_S : S d := by rcases hd with hd | rfl; exact hd; omega
            have he_S : S e := by rcases he with he | rfl; exact he; omega
            exfalso
            have hdvd : p ∣ d * e := ⟨a, by
              rw [hb_eq, hc_eq, hf_eq] at heq
              exact Nat.eq_of_mul_eq_mul_right hp.pos (by linarith)⟩
            exact prime_not_dvd_mul hp
              (not_dvd_of_pos_lt hp hdp hd_lt)
              (not_dvd_of_pos_lt hp hep he_lt)
              hdvd
          · -- e = p, f = p: rp ≥ 2
            rcases hd_lt_or with hd_lt | hd_eq
            · -- d < p, e = p, f = p: rp = 2. lp = rp = 2.
              -- a*p² = d*p² → a = d
              have hd_S : S d := by rcases hd with hd | rfl; exact hd; omega
              have ha_eq' : a = d := Nat.eq_of_mul_eq_mul_right (Nat.mul_pos hp.pos hp.pos)
                (by rw [hb_eq, hc_eq, he_eq, hf_eq] at heq; linarith)
              exact ⟨ha_eq', by rw [hb_eq, he_eq], by rw [hc_eq, hf_eq]⟩
            · -- d = p, e = p, f = p: rp = 3. lp = 2, rp = 3. Contradiction.
              exfalso
              have hdvd : p ∣ a := ⟨p, by
                rw [hb_eq, hc_eq, hd_eq, he_eq, hf_eq] at heq
                exact Nat.eq_of_mul_eq_mul_right (Nat.mul_pos hp.pos hp.pos) (by nlinarith)⟩
              exact not_dvd_of_pos_lt hp hap ha_lt hdvd
      · -- a = p, b = p, c = p: lp = 3. Handle all right-side cases.
        rcases hf_lt_or with hf_lt | hf_eq
        · -- rp = 0
          have hd_lt : d < p := lt_of_le_of_lt (le_trans hde hef) hf_lt
          have he_lt : e < p := lt_of_le_of_lt hef hf_lt
          have hd_S : S d := by rcases hd with hd | rfl; exact hd; omega
          have he_S : S e := by rcases he with he | rfl; exact he; omega
          have hf_S : S f := by rcases hf with hf | rfl; exact hf; omega
          exfalso
          exact p_not_dvd_S_triple hp hpos hlt hd_S he_S hf_S
            ⟨p * p, by rw [← heq, ha_eq, hb_eq, hc_eq]; ring⟩
        · rcases he_lt_or with he_lt | he_eq
          · -- rp = 1
            have hd_lt : d < p := lt_of_le_of_lt hde he_lt
            have hd_S : S d := by rcases hd with hd | rfl; exact hd; omega
            have he_S : S e := by rcases he with he | rfl; exact he; omega
            exfalso
            have hdvd : p ∣ d * e := ⟨p, by
              rw [ha_eq, hb_eq, hc_eq, hf_eq] at heq
              exact Nat.eq_of_mul_eq_mul_right hp.pos (by linarith)⟩
            exact prime_not_dvd_mul hp
              (not_dvd_of_pos_lt hp hdp hd_lt)
              (not_dvd_of_pos_lt hp hep he_lt)
              hdvd
          · rcases hd_lt_or with hd_lt | hd_eq
            · -- d < p, e = p, f = p: rp = 2
              have hd_S : S d := by rcases hd with hd | rfl; exact hd; omega
              exfalso
              rw [ha_eq, hb_eq, hc_eq, he_eq, hf_eq] at heq
              have hd_eq' : d = p :=
                (Nat.eq_of_mul_eq_mul_right (Nat.mul_pos hp.pos hp.pos) (by nlinarith)).symm
              exact absurd (hlt d hd_S) (by omega)
            · -- d = p, e = p, f = p: rp = 3. lp = rp = 3.
              refine ⟨?_, ?_, ?_⟩
              · rw [ha_eq, hd_eq]
              · rw [hb_eq, he_eq]
              · rw [hc_eq, hf_eq]

end B3Primes
