import Mathlib

-- 0. 問題文
-- 0.1. Tの定義
inductive TermT where
  | B : TermT
  | C : TermT
  | I : TermT
  | app : TermT → TermT → TermT

-- 0.2. Uの定義
inductive TermU : Type
  | Z : TermU
  | arr : TermU → TermU → TermU

-- 0.3. [[·]]の定義
def interp : TermT → Set TermU
  | TermT.B => {u | ∃ a b c : TermU, u = TermU.arr (TermU.arr b c) (TermU.arr (TermU.arr a b) (TermU.arr a c))}
  | TermT.C => {u | ∃ a b c : TermU, u = TermU.arr (TermU.arr a (TermU.arr b c)) (TermU.arr b (TermU.arr a c))}
  | TermT.I => {u | ∃ a : TermU, u = TermU.arr a a}
  | TermT.app M N => {b | ∃ a : TermU, TermU.arr a b ∈ interp M ∧ a ∈ interp N}

-- 0.4. 集合X1,X2,X3,X4の定義
def X1 : Set TermU := {TermU.arr TermU.Z TermU.Z}
def X2 : Set TermU := {u | ∃ a b : TermU, u = TermU.arr a (TermU.arr b (TermU.arr b a))}
def X3 : Set TermU := {u | ∃ a b : TermU, u = TermU.arr (TermU.arr (TermU.arr a b) b) a}
def X4 : Set TermU := {u | ∃ a b c d : TermU, u = TermU.arr (TermU.arr a (TermU.arr b (TermU.arr c d))) (TermU.arr c (TermU.arr b (TermU.arr a d)))}

-- 1. 問1
-- 1.1. ZにZ → Zを代入する写像の定義
def subst : TermU → TermU
  | TermU.Z => TermU.arr TermU.Z TermU.Z
  | TermU.arr a b => TermU.arr (subst a) (subst b)

-- 1.2. 代入後も[[·]]に含まれることの証明
theorem substInterp : ∀ M : TermT, ∀ u ∈ interp M, subst u ∈ interp M := by
  intro M
  induction M with
  | B =>
    intro u hu
    rcases hu with ⟨a, b, c, rfl⟩
    dsimp [subst]
    exact ⟨subst a, subst b, subst c, rfl⟩
  | C =>
    intro u hu
    rcases hu with ⟨a, b, c, rfl⟩
    dsimp [subst]
    exact ⟨subst a, subst b, subst c, rfl⟩
  | I =>
    intro u hu
    rcases hu with ⟨a, rfl⟩
    dsimp [subst]
    exact ⟨subst a, rfl⟩
  | app M N ihM ihN =>
    intro u hu
    rcases hu with ⟨a, haM, haN⟩
    have h1 : subst (TermU.arr a u) ∈ interp M := ihM (TermU.arr a u) haM
    have h2 : subst a ∈ interp N := ihN a haN
    exact ⟨subst a, h1, h2⟩

-- 1.3. 問1の解答
theorem prob1 : ¬ ∃ M : TermT, interp M = X1 := by
  rintro ⟨M, heq⟩
  -- 反例の構成
  let counterEx1 : TermU := TermU.arr (TermU.arr TermU.Z TermU.Z) (TermU.arr TermU.Z TermU.Z)
  -- counterEx1 ∈ interp M を示す
  have hCounterExInInterpM : counterEx1 ∈ interp M := by
    have h1 : TermU.arr TermU.Z TermU.Z ∈ interp M := by
      rw [heq]
      rfl
    exact substInterp M (TermU.arr TermU.Z TermU.Z) h1
  -- counterEx1 ∉ X1 を示す
  have hCounterExNotInX1 : counterEx1 ∉ X1 := by
    simp [X1, counterEx1]
  -- counterEx1 ∈ interp M かつ counterEx1 ∉ X1 なので、interp M ≠ X1
  have hCounterExInX1 : counterEx1 ∈ X1 := by
    rw [← heq]
    exact hCounterExInInterpM
  exact hCounterExNotInX1 hCounterExInX1

-- 2. 問2
-- 2.1. 正・負の出現の差の定義（不変量）
def pred : TermU → Int
  | TermU.Z => 1
  | TermU.arr a b => pred b - pred a

-- 2.2. [[·]]が生成する集合はpredの値が0であること
theorem predZero : ∀ M : TermT, ∀ u ∈ interp M, pred u = 0 := by
  intro M
  induction M with
  | B =>
    intro u hu
    rcases hu with ⟨a, b, c, rfl⟩
    simp only [pred]
    ring
  | C =>
    intro u hu
    rcases hu with ⟨a, b, c, rfl⟩
    simp only [pred]
    ring
  | I =>
    intro u hu
    rcases hu with ⟨a, rfl⟩
    simp only [pred]
    ring
  | app M N ihM ihN =>
    intro u hu
    rcases hu with ⟨a, haM, haN⟩
    have h1 : pred (TermU.arr a u) = 0 := ihM (TermU.arr a u) haM
    have h2 : pred a = 0 := ihN a haN
    dsimp [pred] at h1
    rw [h2] at h1
    simp only [Int.sub_zero] at h1
    exact h1

-- 2.3. 問2の解答
theorem prob2 : ¬ ∃ M : TermT, interp M = X2 := by
  rintro ⟨M, heq⟩
  -- 反例の構成
  let a0 : TermU := TermU.arr TermU.Z TermU.Z
  let b1 : TermU := TermU.Z
  let counterEx2 : TermU := TermU.arr a0 (TermU.arr b1 (TermU.arr b1 a0))
  -- counterEx2 ∈ X2 を示す
  have hCounterExInX2 : counterEx2 ∈ X2 := by
    dsimp [X2]
    exact ⟨a0, b1, rfl⟩
  -- counterEx2 ∉ interp M を示す
  have hCounterExNotInInterpM : counterEx2 ∉ interp M := by
    rintro h_in
    have hPred : pred counterEx2 = 0 := predZero M counterEx2 h_in
    have hPred_counterEx : pred counterEx2 = -2 := by
      rfl
    contradiction
  -- counterEx2 ∈ X2 かつ counterEx2 ∉ interp M なので、interp M ≠ X2
  have hCounterExInInterpM : counterEx2 ∈ interp M := by
    rw [heq]
    exact hCounterExInX2
  exact hCounterExNotInInterpM hCounterExInInterpM

-- 3. 問3
-- 3.1. 付値の定義
def val : TermU → Bool
  | TermU.Z => false
  | TermU.arr a b => !val a || val b

-- 3.2. 健全性
theorem soundness : ∀ M : TermT, ∀ u ∈ interp M, val u = true := by
  intro M
  induction M with
  | B =>
    intro u hu
    rcases hu with ⟨a, b, c, rfl⟩
    simp only [val]
    cases val a <;> cases val b <;> cases val c <;>
    rfl
  | C =>
    intro u hu
    rcases hu with ⟨a, b, c, rfl⟩
    simp only [val]
    cases val a <;> cases val b <;> cases val c <;>
    rfl
  | I =>
    intro u hu
    rcases hu with ⟨a, rfl⟩
    simp only [val]
    cases val a <;>
    rfl
  | app M N ihM ihN =>
    intro u hu
    rcases hu with ⟨a, haM, haN⟩
    have h1 : val (TermU.arr a u) = true := ihM (TermU.arr a u) haM
    have h2 : val a = true := ihN a haN
    simp only [val] at h1
    rw [h2] at h1
    simp only [Bool.not_true, Bool.false_or] at h1
    exact h1

-- 3.3. 問3の解答
theorem prob3 : ¬ ∃ M : TermT, interp M = X3 := by
  rintro ⟨M, heq⟩
  -- 反例の構成
  let aF : TermU := TermU.Z
  let bT : TermU := TermU.arr TermU.Z TermU.Z
  let counterEx3 : TermU := TermU.arr (TermU.arr (TermU.arr aF bT) bT) aF
  -- counterEx3 ∈ X3 を示す
  have hCounterExInX3 : counterEx3 ∈ X3 := by
    dsimp [X3]
    exact ⟨aF, bT, rfl⟩
  -- counterEx3 ∉ interp M を示す
  have hCounterExNotInInterpM : counterEx3 ∉ interp M := by
    rintro h_in
    have h_true : val counterEx3 = true := soundness M counterEx3 h_in
    have h_false : val counterEx3 = false := by
      rfl
    contradiction
  -- counterEx3 ∈ X3 かつ counterEx3 ∉ interp M なので、interp M ≠ X3
  have hCounterExInInterpM : counterEx3 ∈ interp M := by
    rw [heq]
    exact hCounterExInX3
  exact hCounterExNotInInterpM hCounterExInInterpM

  -- 4. 問4
theorem prob4 : ∃ M : TermT, interp M = X4 := by
  let BC : TermT := TermT.app TermT.B TermT.C
  let h : TermT := TermT.app (TermT.app TermT.B BC) TermT.C
  let ans : TermT := TermT.app BC h
  use ans
  ext u
  dsimp [ans, h, BC]
  simp only [interp, Set.mem_setOf_eq, TermU.arr.injEq, ↓existsAndEq, true_and, and_true,
    exists_eq_right', X4]
  constructor
  · rintro ⟨a, b, c, d, rfl⟩
    exact ⟨c, a, b, d, rfl⟩
  · rintro ⟨a, b, c, d, rfl⟩
    exact ⟨b, c, a, d, rfl⟩
