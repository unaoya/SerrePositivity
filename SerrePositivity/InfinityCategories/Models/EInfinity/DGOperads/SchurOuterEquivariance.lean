module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.TensorFamilyTensorAdjacent
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.CompositionAdjacentBlockEquivariance
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.SchurAction

/-!
模型。文献の定義との比較は後で
# Schur 演算の生成射の外側等変性

概要：Berger–Moerdijk §1 の自由代数の演算で外側の隣接入力の交換を消す。
方針：係数と入力を分離し、合成と連結のブロック交換を Schur 図式の関係で消す。
規約：交換後の入力族は同じ隣接互換で引き戻す。
使われ方：Schur 作用の対称群に関する代数公理を証明する。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.MonoidalCategory
open _root_.SerrePositivity.DifferentialGraded _root_.SerrePositivity.TensorPowers _root_.SerrePositivity.Coxeter
open scoped _root_.BigOperators

variable {A : Type u} [CommRing A]

attribute [local implicit_reducible] SerrePositivity.SymmetricSequence
  SerrePositivity.SymmetricSequence.level
attribute [local irreducible] HomologicalComplex.monoidalCategoryStruct

/-- 概要：有限全単射の対角作用は始域と終域の長さの表記が違っても Schur 生成射で消える（Berger–Moerdijk §1）。
方針：Schur 図式の余極限の可換性を全単射の射に適用する。
規約：全単射は Fin m と Fin n の間に指定する。
使われ方：入力のブロック交換を Schur 演算の出力で相殺する。 -/
lemma arityBijectionMap_schurι (P : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A) (K : Complex A) {m n : ℕ}
    (e : Fin m ≃ Fin n) :
    (P.arityBijectionMap e ⊗ₘ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorPowerEquivMap K e) ≫
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurι A P.sequence K n = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurι A P.sequence K m := by
  exact colimit.w (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurDiagram A P.sequence K)
    (_root_.SerrePositivity.FiniteBijection.homOfEquiv (X := _root_.SerrePositivity.FiniteBijection.of m) (Y := _root_.SerrePositivity.FiniteBijection.of n) e)

private lemma operation_outer_invariance
    {C C' U U' V V' W W' R R' Z Z' Y : Complex A}
    (u : U ⟶ V ⊗ W) (u' : U' ⟶ V' ⊗ W')
    (f : C ⊗ V ⟶ R) (f' : C' ⊗ V' ⟶ R')
    (l : W ⟶ Z) (l' : W' ⟶ Z') (q : R ⊗ Z ⟶ Y) (q' : R' ⊗ Z' ⟶ Y)
    (a : C ⟶ C') (t : U ⟶ U') (b : V ⟶ V') (c : W ⟶ W')
    (r : R ⟶ R') (z : Z ⟶ Z')
    (hu : t ≫ u' = u ≫ (b ⊗ₘ c)) (hf : (a ⊗ₘ b) ≫ f' = f ≫ r)
    (hl : c ≫ l' = l ≫ z) (hq : (r ⊗ₘ z) ≫ q' = q) :
    (a ⊗ₘ t) ≫ (C' ◁ u') ≫ (α_ C' V' W').inv ≫ (f' ⊗ₘ l') ≫ q' =
      (C ◁ u) ≫ (α_ C V W).inv ≫ (f ⊗ₘ l) ≫ q := by
  have htu : (a ⊗ₘ t) ≫ (C' ◁ u') = (C ◁ u) ≫ (a ⊗ₘ (b ⊗ₘ c)) := by
    rw [tensorHom_comp_whiskerLeft, hu, ← whiskerLeft_comp_tensorHom]
  rw [← Category.assoc _ _ ((α_ C' V' W').inv ≫ (f' ⊗ₘ l') ≫ q'), htu]
  simp only [Category.assoc]
  rw [associator_inv_naturality_assoc]
  rw [← Category.assoc _ (f' ⊗ₘ l') q', tensorHom_comp_tensorHom, hf, hl,
    ← tensorHom_comp_tensorHom, Category.assoc, hq]

/-- 概要：Schur 演算の生成射は外側の隣接入力の同時交換で変わらない（Berger–Moerdijk §1）。
方針：分離同型、合成、テンソル冪の連結の隣接交換の等変性を組み合わせる。
規約：係数の置換と入力の対の交換に同じ隣接互換を用いる。
使われ方：自由代数の作用の外側等変性を生成射上で証明する。 -/
lemma schurOperationGenerator_adjacent_equivariance (P : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A) (K : Complex A)
    (n : ℕ) (s : Fin (n + 1) → ℕ) (i : Fin n) :
    (P.sequence.map (_root_.SerrePositivity.FiniteBijection.permutation (n + 1) (adjacentTransposition i)) ⊗ₘ
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyAdjacentIso n (fun j => P.arity (s j) ⊗ power K (s j)) i).hom) ≫
      P.schurOperationGenerator K (n + 1) (fun j => s (adjacentTransposition i j)) =
    P.schurOperationGenerator K (n + 1) s := by
  exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.operation_outer_invariance
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyTensorIso (n + 1) (fun j => P.arity (s j)) (fun j => power K (s j))).hom
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyTensorIso (n + 1) (fun j => P.arity (s (adjacentTransposition i j)))
      (fun j => power K (s (adjacentTransposition i j)))).hom
    (P.composition (n + 1) s) (P.composition (n + 1) (fun j => s (adjacentTransposition i j)))
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorPowerFamilyIso K (n + 1) s).hom
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorPowerFamilyIso K (n + 1) (fun j => s (adjacentTransposition i j))).hom
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurι A P.sequence K (∑ j, s j))
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurι A P.sequence K (∑ j, s (adjacentTransposition i j)))
    _ _ _ _ _ _
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyTensorIso_adjacent n (fun j => P.arity (s j)) (fun j => power K (s j)) i)
    (P.composition_adjacent_block_equivariance n s i)
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorPowerFamilyIso_adjacent K n s i)
    (P.arityBijectionMap_schurι K (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyAdjacentBlockEquiv n s i))

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad
