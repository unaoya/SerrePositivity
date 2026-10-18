module

public import SerrePositivity.EInfinity.Operad.TensorFamilyTensorAdjacent
public import SerrePositivity.EInfinity.Operad.CompositionAdjacentBlockEquivariance
public import SerrePositivity.EInfinity.Operad.SchurAction

/-!
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

namespace SerrePositivity.EInfinity.Operad

open CategoryTheory Limits MonoidalCategory
open SerrePositivity.DifferentialGraded SerrePositivity.TensorPowers SerrePositivity.Coxeter
open scoped BigOperators

variable {A : Type u} [CommRing A]

attribute [local implicit_reducible] SerrePositivity.SymmetricSequence
  SerrePositivity.SymmetricSequence.level
attribute [local irreducible] HomologicalComplex.monoidalCategoryStruct

/-- 概要：有限全単射の対角作用は始域と終域の長さの表記が違っても Schur 生成射で消える（Berger–Moerdijk §1）。
方針：Schur 図式の余極限の可換性を全単射の射に適用する。
規約：全単射は Fin m と Fin n の間に指定する。
使われ方：入力のブロック交換を Schur 演算の出力で相殺する。 -/
lemma arityBijectionMap_schurι (P : Operad A) (K : Complex A) {m n : ℕ}
    (e : Fin m ≃ Fin n) :
    (P.arityBijectionMap e ⊗ₘ tensorPowerEquivMap K e) ≫
      schurι A P.sequence K n = schurι A P.sequence K m := by
  exact colimit.w (schurDiagram A P.sequence K)
    (FiniteBijection.homOfEquiv (X := FiniteBijection.of m) (Y := FiniteBijection.of n) e)

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
lemma schurOperationGenerator_adjacent_equivariance (P : Operad A) (K : Complex A)
    (n : ℕ) (s : Fin (n + 1) → ℕ) (i : Fin n) :
    (P.sequence.map (FiniteBijection.permutation (n + 1) (adjacentTransposition i)) ⊗ₘ
      (tensorFamilyAdjacentIso n (fun j => P.arity (s j) ⊗ power K (s j)) i).hom) ≫
      P.schurOperationGenerator K (n + 1) (fun j => s (adjacentTransposition i j)) =
    P.schurOperationGenerator K (n + 1) s := by
  exact operation_outer_invariance
    (tensorFamilyTensorIso (n + 1) (fun j => P.arity (s j)) (fun j => power K (s j))).hom
    (tensorFamilyTensorIso (n + 1) (fun j => P.arity (s (adjacentTransposition i j)))
      (fun j => power K (s (adjacentTransposition i j)))).hom
    (P.composition (n + 1) s) (P.composition (n + 1) (fun j => s (adjacentTransposition i j)))
    (tensorPowerFamilyIso K (n + 1) s).hom
    (tensorPowerFamilyIso K (n + 1) (fun j => s (adjacentTransposition i j))).hom
    (schurι A P.sequence K (∑ j, s j))
    (schurι A P.sequence K (∑ j, s (adjacentTransposition i j)))
    _ _ _ _ _ _
    (tensorFamilyTensorIso_adjacent n (fun j => P.arity (s j)) (fun j => power K (s j)) i)
    (P.composition_adjacent_block_equivariance n s i)
    (tensorPowerFamilyIso_adjacent K n s i)
    (P.arityBijectionMap_schurι K (tensorFamilyAdjacentBlockEquiv n s i))

end SerrePositivity.EInfinity.Operad
