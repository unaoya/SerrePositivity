module

public import Mathlib.AlgebraicTopology.DoldKan.Normalized
public import Mathlib.AlgebraicTopology.DoldKan.Degeneracies

/-!
# 退化単体を消す射の正規化への降下

概要：Berger–Fresse §1.1.4 の AW 公式を正規化鎖へ降ろすための一般補題を与える。
方針：Dold–Kan の恒等射の分解を用い、退化写像から来る項を消去する。
規約：加法圏での射の等式として述べ、環や単体集合の基底に依存しない。
使われ方：AW 成分が退化単体を消すことを示した後、その生成元公式を正規化上で得る。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.SimplicialChains.AlexanderWhitney

open _root_.CategoryTheory _root_.CategoryTheory.Preadditive
open _root_.AlgebraicTopology _root_.AlgebraicTopology.DoldKan
open scoped _root_.Simplicial

/-- 概要：退化写像を消す射は正規化射影の前置で変わらない（Berger–Fresse §1.1.4）。
方針：恒等射を正規化射影と退化写像を経る有限和へ分解する。
規約：次数零では退化条件は空、正次数では全ての退化位置を扱う。
使われ方：生成元で定義した AW 公式の正規化への降下を保証する。 -/
lemma projector_comp_of_degeneracies_zero
    {C : Type*} [Category* C] [Preadditive C] (X : SimplicialObject C)
    {Z : C} (n : ℕ) (f : X _⦋n⦌ ⟶ Z)
    (h : ∀ (k : ℕ) (e : k + 1 = n) (i : Fin (k + 1)),
      X.σ i ≫ eqToHom (congrArg (fun j => X _⦋j⦌) e) ≫ f = 0) :
    (PInfty.f n : X _⦋n⦌ ⟶ _) ≫ f = f := by
  cases n with
  | zero => simp only [PInfty_f_0, Category.id_comp]
  | succ n =>
    have hz (i : Fin (n + 1)) : X.σ i ≫ f = 0 := by
      simpa using h n rfl i
    have hid := congrArg (fun g => g ≫ f) (MorphComponents.id_φ X n)
    simp only [MorphComponents.φ, MorphComponents.id, add_comp, sum_comp,
      Category.assoc, hz, Limits.comp_zero, Finset.sum_const_zero, add_zero,
      Category.id_comp] at hid
    simpa only [← Category.assoc, PInfty_f_idem] using hid

/-- 概要：退化成分を消す射を正規化 Moore 成分に制限する（Berger–Fresse §1.1.4）。
方針：Moore 部分複体からの包含を前置する。
規約：この定義自体には退化条件を要求せず、降下の等式に条件を課す。
使われ方：AW の正規化成分の射を定義する。 -/
def restrictToNormalized {C : Type*} [Category* C] [Abelian C]
    (X : SimplicialObject C) {Z : C} (n : ℕ) (f : X _⦋n⦌ ⟶ Z) :
    ((normalizedMooreComplex C).obj X).X n ⟶ Z :=
  (inclusionOfMooreComplexMap X).f n ≫ f

/-- 概要：退化成分を消す射の正規化への降下は元の射を復元する（Berger–Fresse §1.1.4）。
方針：正規化射影と包含の合成が P∞ であることを使う。
規約：退化条件には次数移送を含めて零次にも同じ型を使う。
使われ方：正規化 AW 成分の生成元公式を計算する。 -/
lemma normalization_restrictToNormalized {C : Type*} [Category* C] [Abelian C]
    (X : SimplicialObject C) {Z : C} (n : ℕ) (f : X _⦋n⦌ ⟶ Z)
    (h : ∀ (k : ℕ) (e : k + 1 = n) (i : Fin (k + 1)),
      X.σ i ≫ eqToHom (congrArg (fun j => X _⦋j⦌) e) ≫ f = 0) :
    (PInftyToNormalizedMooreComplex X).f n ≫ _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.restrictToNormalized X n f = f := by
  have hp := congrArg (fun g => g.f n)
    (PInftyToNormalizedMooreComplex_comp_inclusionOfMooreComplexMap X)
  change (PInftyToNormalizedMooreComplex X).f n ≫
    (inclusionOfMooreComplexMap X).f n = PInfty.f n at hp
  rw [_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.restrictToNormalized, ← Category.assoc, hp]
  exact _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.projector_comp_of_degeneracies_zero X n f h

end SerrePositivity.SimplicialChains.AlexanderWhitney
