module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Composition
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.PartialCompositionTransport
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.TensorFamilySubstitutionNested

/-!
模型。文献の定義との比較は後で
# 空の入力族の入れ子の合成

概要：Berger–Moerdijk §1 の反復合成と部分合成の結合則の空の入力族の場合を証明する。
方針：空の反復合成を右単位子へ簡約し、その自然性とモノイダル整合性を使う。
規約：内側の未代入入力 k 個は零個でもよい。
使われ方：反復合成の入れ子の結合則の入力数に関する帰納法の基底となる。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory
open _root_.SerrePositivity.DifferentialGraded
open scoped _root_.BigOperators

variable {A : Type u} [CommRing A]

attribute [local implicit_reducible] SerrePositivity.SymmetricSequence
  SerrePositivity.SymmetricSequence.level
attribute [local irreducible] HomologicalComplex.monoidalCategoryStruct

/-- 概要：空の入力族への反復合成は外側の先頭入力への部分合成と可換である（Berger–Moerdijk §1）。
方針：有限和を零に簡約し、右単位子の自然性を適用する。
規約：外側には m+1 入力、内側には未代入入力 k 個がある。
使われ方：入れ子の反復合成の結合則の帰納法を開始する。 -/
lemma composeFirstInputs_nested_zero (P : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A) (m k : ℕ) (s : Fin 0 → ℕ) :
    (P.comp m (0 + k) 0 ▷ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily 0 (fun i => P.arity (s i))) ≫
      (eqToHom (congrArg P.arity (by omega : m + (0 + k) = 0 + (m + k))) ▷
        _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily 0 (fun i => P.arity (s i))) ≫
      P.composeFirstInputs 0 (m + k) s ≫
        eqToHom (congrArg P.arity (by simp : (∑ i, s i) + (m + k) = m + ((∑ i, s i) + k))) =
    (α_ (P.arity (m + 1)) (P.arity (0 + k)) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily 0 (fun i => P.arity (s i)))).hom ≫
      (P.arity (m + 1) ◁ P.composeFirstInputs 0 k s) ≫ P.comp m ((∑ i, s i) + k) 0 := by
  unfold _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.composeFirstInputs
  dsimp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily]
  simp only [Category.assoc]
  rw [rightUnitor_naturality_assoc, rightUnitor_naturality_assoc]
  simp only [eqToHom_refl, Category.comp_id]
  have hu : (ρ_ (P.arity (m + 1) ⊗ P.arity (0 + k))).hom =
      (α_ (P.arity (m + 1)) (P.arity (0 + k)) (𝟙_ (Complex A))).hom ≫
        (P.arity (m + 1) ◁ (ρ_ (P.arity (0 + k))).hom) := by monoidal
  rw [hu]
  simp only [Category.assoc, Category.id_comp]
  conv_lhs =>
    arg 2
    arg 2
    arg 2
    rw [eqToHom_trans]
  have hc := P.comp_index_eq (Eq.refl m)
    (by simp : 0 + k = (∑ i, s i) + k) (0 : Fin (m + 1))
  simp only [eqToHom_refl, tensorHom_id, id_whiskerRight, Fin.cast_refl,
    Category.id_comp] at hc
  exact congrArg ((α_ (P.arity (m + 1)) (P.arity (0 + k)) (𝟙_ (Complex A))).hom ≫
    (P.arity (m + 1) ◁ (ρ_ (P.arity (0 + k))).hom) ≫ ·) hc.symm

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad
