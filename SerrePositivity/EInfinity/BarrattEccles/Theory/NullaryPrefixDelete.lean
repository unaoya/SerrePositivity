module

public import SerrePositivity.EInfinity.BarrattEccles.Theory.NullaryFamilyAdjacent
public import SerrePositivity.EInfinity.BarrattEccles.OperadStructure
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.CompositionAdjacentEquivariance
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.CompositionAdjacentValues
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.CompositionTailBijection
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.TensorUnitFamily

/-!
# 先頭の入力を零入力へ代入する係数射

## 概要
HA 3.2.4.7 の二色比較で、先頭の一方の色の入力を零入力演算へ代入する。

## 方針
指定された零入力の単位を有限テンソルして反復合成へ代入し、消去した入力の交換不変性を示す。

## 規約
arity 0 の増大の逆を使い、消去する色の入力数が零の場合も含める。

## 使われ方
Hopf 対角の両因子を二つの色の係数へ射影する比較射。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity
open CategoryTheory MonoidalCategory
open SerrePositivity.DifferentialGraded SerrePositivity.Coxeter
open scoped BigOperators
attribute [local implicit_reducible] SerrePositivity.SymmetricSequence
  SerrePositivity.SymmetricSequence.level

/-- 単位からの係数族を、任意の係数の右側へ挿入する。 -/
def coefficientUnitInsert {A : Type u} [CommRing A] (X V : Complex A)
    (η : 𝟙_ (Complex A) ⟶ V) : X ⟶ X ⊗ V :=
  (ρ_ X).inv ≫ (X ◁ η)

/-- 単位からの係数族の挿入は、元の係数の全射に自然。 -/
@[reassoc]
lemma coefficientUnitInsert_naturality {A : Type u} [CommRing A] {X Y V : Complex A}
    (η : 𝟙_ (Complex A) ⟶ V) (f : X ⟶ Y) :
    f ≫ coefficientUnitInsert Y V η = coefficientUnitInsert X V η ≫ (f ▷ V) := by
  unfold coefficientUnitInsert
  rw [rightUnitor_inv_naturality_assoc, ← whisker_exchange]
  simp only [Category.assoc]

namespace BarrattEccles
variable (A : Type u) [CommRing A]
attribute [local implicit_reducible] operad sequence

/-- 消去する各入力に代入する、零入力係数の指定された族。 -/
def nullaryInputFamily (n : ℕ) :
    𝟙_ (Complex A) ⟶ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily n (fun _ => (operad A).arity 0) :=
  (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorUnitFamilyIso A n).inv ≫ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyMap n (fun _ => (nullaryCoefficientIso A).inv)

/-- 先頭 n 個の入力を零入力へ代入して、後ろの k 入力を残す。 -/
def nullaryPrefixDelete (n k : ℕ) : (operad A).arity (n + k) ⟶ (operad A).arity k :=
  coefficientUnitInsert _ _ (nullaryInputFamily A n) ≫
    (operad A).composeFirstInputs n k (fun _ => 0) ≫
      eqToHom (congrArg (operad A).arity (by simp : (∑ _ : Fin n, 0) + k = k))

/-- 消去する零長ブロックの隣接交換は、出力には恒等全単射を誘導する。 -/
lemma nullaryAdjacentOutput (n k : ℕ) (i : Fin n) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadCompositionAdjacentOutput n k (fun _ : Fin (n + 1) => 0) i = Equiv.refl _ := by
  ext x
  simpa only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadAdjacentPrefixLength, Finset.sum_const_zero, Nat.add_zero,
    Nat.not_lt_zero, ite_false, Equiv.refl_apply] using
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadCompositionAdjacentOutput_val n k (fun _ => 0) i x

/-- 先頭の消去する入力の各隣接交換は、指定係数射を保つ。 -/
lemma nullaryPrefixDelete_adjacent (n k : ℕ) (i : Fin n) :
    (operad A).sequence.map (FiniteBijection.permutation (n + 1 + k)
      (FiniteBijection.blockEquiv (adjacentTransposition i) (Equiv.refl (Fin k)))) ≫
        nullaryPrefixDelete A (n + 1) k = nullaryPrefixDelete A (n + 1) k := by
  have h := (operad A).composeFirstInputs_adjacent_equivariance n k (fun _ => 0) i
  have hzero : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyAdjacentIso n (fun _ : Fin (n + 1) =>
      (operad A).arity 0) i).hom = 𝟙 _ := nullaryFamilyAdjacent_hom A n i
  rw [hzero, tensorHom_id, nullaryAdjacentOutput,
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.arityBijectionMap_refl, Category.comp_id] at h
  unfold nullaryPrefixDelete
  erw [coefficientUnitInsert_naturality_assoc]
  have hh := congrArg
    (fun t => coefficientUnitInsert _ _ (nullaryInputFamily A (n + 1)) ≫ t ≫
      eqToHom (congrArg (operad A).arity
        (by simp : (∑ _ : Fin (n + 1), 0) + k = k))) h
  dsimp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.arity, SerrePositivity.SymmetricSequence.level] at hh ⊢
  simpa only [Category.assoc] using hh

/-- 先頭の消去する入力の任意の置換は、指定係数射を保つ。 -/
lemma nullaryPrefixDelete_prefix_invariant (n k : ℕ) (σ : Equiv.Perm (Fin n)) :
    (operad A).sequence.map (FiniteBijection.permutation (n + k)
      (FiniteBijection.blockEquiv σ (Equiv.refl (Fin k)))) ≫
        nullaryPrefixDelete A n k = nullaryPrefixDelete A n k := by
  have hid (r : ℕ) : (operad A).sequence.map
      (FiniteBijection.permutation r (Equiv.refl (Fin r))) = 𝟙 ((operad A).arity r) := by
    change (operad A).sequence.map (FiniteBijection.permutation r 1) = _
    rw [FiniteBijection.permutation_one, CategoryTheory.Functor.map_id]
    rfl
  cases n with
  | zero =>
    have hσ : σ = 1 := Subsingleton.elim _ _
    simp only [hσ, show (1 : Equiv.Perm (Fin 0)) = Equiv.refl _ from rfl,
      FiniteBijection.blockEquiv_refl, hid]
    exact Category.id_comp _
  | succ n =>
    have hσ : σ ∈ Submonoid.closure (Set.range (@adjacentTransposition n)) := by
      rw [show (@adjacentTransposition n) =
        (fun i : Fin n => Equiv.swap i.castSucc i.succ) from rfl,
        Equiv.Perm.mclosure_swap_castSucc_succ]
      exact Submonoid.mem_top σ
    induction hσ using Submonoid.closure_induction with
    | mem τ hτ =>
      obtain ⟨i, rfl⟩ := hτ
      exact nullaryPrefixDelete_adjacent A n k i
    | one =>
      simp only [show (1 : Equiv.Perm (Fin (n + 1))) = Equiv.refl _ from rfl,
        FiniteBijection.blockEquiv_refl, hid]
      exact Category.id_comp _
    | mul σ τ _ _ hσ hτ =>
      have he : FiniteBijection.blockEquiv (σ * τ) (Equiv.refl (Fin k)) =
          FiniteBijection.blockEquiv σ (Equiv.refl (Fin k)) *
            FiniteBijection.blockEquiv τ (Equiv.refl (Fin k)) := by
        have hmul : (Equiv.refl (Fin k)) * (Equiv.refl (Fin k)) = Equiv.refl _ := by
          ext x
          rfl
        simpa only [hmul] using FiniteBijection.blockEquiv_mul σ τ
          (Equiv.refl (Fin k)) (Equiv.refl (Fin k))
      rw [he, FiniteBijection.permutation_mul, CategoryTheory.Functor.map_comp,
        Category.assoc, hσ, hτ]

end BarrattEccles
end SerrePositivity.EInfinity
