module

public import SerrePositivity.InfinityCategories.HA.Monads.WalkingAdjunctionLevels

/-!
概要：全次数の射を有限個の原子的な射の語へ分解する。
方針：水平合成の長さの加法性に関する強い帰納法を使う。
規約：ここで証明するのは分解の存在であり、一意性や退化との両立は別に検収する。
使われ方：Riehl–Verity Definition 2.1.4・Proposition 3.1.10、HA Proposition 4.7.3.3、
Kerodon Remark 6.2.1.4（Tag 02EN）の前の全coherenceの構成。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory

namespace SerrePositivity.InfinityCategories.HA.Monads

/-- 概要：水平合成に関して原子的なn次元の射。
方針：非単位であり、二つに分解すれば一方は単位となる条件を使う。
規約：長さ0は実際に単位を検出する。使われ方：Riehl–Verity Definition 2.1.4。 -/
def WalkingAdjunctionLevelIsAtomic {n : ℕ} {X Y : WalkingAdjunctionLevel n} (F : X ⟶ Y) : Prop :=
  0 < walkingAdjunctionLevelSize F ∧
    ∀ (Z : WalkingAdjunctionLevel n) (A : X ⟶ Z) (B : Z ⟶ Y), A ≫ B = F →
      walkingAdjunctionLevelSize A = 0 ∨ walkingAdjunctionLevelSize B = 0

/-- 概要：実際の射を像として保持する有限の原子的な語。
方針：空の語・原子的な射・語の合成を帰納的に記録する。
規約：存在の命題だけでなく語のデータの型。使われ方：Riehl–Verity Proposition 3.1.10。 -/
inductive WalkingAdjunctionAtomicWord (n : ℕ) :
    {X Y : WalkingAdjunctionLevel n} → (X ⟶ Y) → Type
  | nil (X : WalkingAdjunctionLevel n) : WalkingAdjunctionAtomicWord n (𝟙 X)
  | atom {X Y : WalkingAdjunctionLevel n} (F : X ⟶ Y) (h : WalkingAdjunctionLevelIsAtomic F) :
      WalkingAdjunctionAtomicWord n F
  | comp {X Y Z : WalkingAdjunctionLevel n} {F : X ⟶ Y} {G : Y ⟶ Z}
      (a : WalkingAdjunctionAtomicWord n F) (b : WalkingAdjunctionAtomicWord n G) :
      WalkingAdjunctionAtomicWord n (F ≫ G)

/-- 概要：全次数の全ての射は原子的な射の有限の語の像となる。
方針：非原子的な正の長さの射を二つの短い射へ分け、長さに強い帰納法を使う。
規約：語の一意性はここでは主張しない。使われ方：Riehl–Verity Proposition 3.1.10。 -/
lemma walkingAdjunctionAtomicWord_nonempty {n : ℕ} {X Y : WalkingAdjunctionLevel n}
    (F : X ⟶ Y) : Nonempty (WalkingAdjunctionAtomicWord n F) := by
  suffices ∀ k, ∀ {X Y : WalkingAdjunctionLevel n} (F : X ⟶ Y),
      walkingAdjunctionLevelSize F = k → Nonempty (WalkingAdjunctionAtomicWord n F) from
    this _ F rfl
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro X Y F hk
    by_cases h₀ : walkingAdjunctionLevelSize F = 0
    · have hXY : X = Y := by
        have h := walkingAdjunctionLevelSize_zero_endpoints F h₀
        cases X
        cases Y
        cases h
        rfl
      subst Y
      have hF : F = 𝟙 X := walkingAdjunctionLevelSize_zero_eq_id F h₀
      subst F
      exact ⟨.nil X⟩
    · by_cases ha : WalkingAdjunctionLevelIsAtomic F
      · exact ⟨.atom F ha⟩
      · have hf : ¬ ∀ (Z : WalkingAdjunctionLevel n) (A : X ⟶ Z) (B : Z ⟶ Y),
            A ≫ B = F → walkingAdjunctionLevelSize A = 0 ∨ walkingAdjunctionLevelSize B = 0 :=
          fun h => ha ⟨Nat.pos_of_ne_zero h₀, h⟩
        push Not at hf
        obtain ⟨Z, A, B, hab, ha₀, hb₀⟩ := hf
        have hs : walkingAdjunctionLevelSize F =
            walkingAdjunctionLevelSize A + walkingAdjunctionLevelSize B := by
          rw [← hab]
          exact walkingAdjunctionLevelSize_comp X.point Z.point Y.point A B
        have hA : walkingAdjunctionLevelSize A < k := by omega
        have hB : walkingAdjunctionLevelSize B < k := by omega
        obtain ⟨a⟩ := ih _ hA A rfl
        obtain ⟨b⟩ := ih _ hB B rfl
        exact ⟨hab ▸ WalkingAdjunctionAtomicWord.comp a b⟩

end SerrePositivity.InfinityCategories.HA.Monads
