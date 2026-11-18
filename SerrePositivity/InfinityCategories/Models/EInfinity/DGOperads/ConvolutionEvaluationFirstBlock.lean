module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.ConvolutionOperations
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.ConvolutionUnitEvaluation
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.ConvolutionAssemblyTensor
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.ConvolutionEvaluationAppend

/-!
模型。文献の定義との比較は後で
# 先頭ブロックへの convolution 演算の評価

概要：Berger–Fresse §3.1 の先頭の convolution 演算と後方の独立な評価を比較する。
方針：先頭の関数の評価を転置前の射へ戻し、後方ブロックの組み立て公式を適用する。
規約：先頭・後方のブロックは空を許す。
使われ方：先頭への部分合成の公理を余代入と代入の二ブロック図式へ移す。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory
open _root_.SerrePositivity.DifferentialGraded _root_.SerrePositivity.TensorPowers

private lemma evaluation_head {C : Type u} [Category.{v} C] [MonoidalCategory C]
    [SymmetricCategory C] {Q F R H S B L : C}
    (f : Q ⟶ F) (e : F ⊗ H ⟶ B) (q : R ⊗ S ⟶ L) :
    (f ▷ R ▷ (H ⊗ S)) ≫ tensorμ F R H S ≫ (e ⊗ₘ q) =
      tensorμ Q R H S ≫ (((f ▷ H) ≫ e) ⊗ₘ q) := by
  have h := tensorμ_natural_left f (𝟙 R) H S
  simp only [id_whiskerRight, tensorHom_id] at h
  rw [reassoc_of% h, ← tensorHom_id, tensorHom_comp_tensorHom]
  simp only [Category.id_comp]

namespace Operad

variable {A : Type u} [CommRing A] {P : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A}

attribute [local irreducible] HomologicalComplex.monoidalCategoryStruct
attribute [local implicit_reducible] _root_.SerrePositivity.TensorPowers.power
attribute [local implicit_reducible] SerrePositivity.SymmetricSequence
  SerrePositivity.SymmetricSequence.level

/-- 概要：先頭の convolution と後方の評価は余代入・反復評価・代入の図式になる（BF §3.1）。
方針：先頭の転置の評価を戻し、独立な後方の評価を組み立ての各段へ通す。
規約：入力の関数と評価点を前半・後半の二ブロックのまま明示する。
使われ方：先頭位置の部分合成則で入力代入と出力余代入を比較する。 -/
lemma convolutionAction_firstBlock_evaluation (hP : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Hopf P) (H : P.Coalgebra)
    (B : P.Algebra) (n m : ℕ) :
    ((α_ (P.arity n) (power (homComplex A H.carrier B.carrier) n)
        (power (homComplex A H.carrier B.carrier) m)).inv ▷ power H.carrier (m + 1)) ≫
      ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.convolutionAction hP H B n ▷ power (homComplex A H.carrier B.carrier) m) ▷
        power H.carrier (m + 1)) ≫ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.convolutionPowerEvaluation H.carrier B.carrier (m + 1) =
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.convolutionAssembly (hP.diagonalComponent n)
      ((α_ (P.arity n) H.carrier (power H.carrier m)).inv ≫
        (H.coaction n ▷ power H.carrier m))
      (tensorμ (power (homComplex A H.carrier B.carrier) n)
          (power (homComplex A H.carrier B.carrier) m) (power H.carrier n) (power H.carrier m) ≫
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.convolutionPowerEvaluation H.carrier B.carrier n ⊗ₘ
          _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.convolutionPowerEvaluation H.carrier B.carrier m))
      ((α_ (P.arity n) (power B.carrier n) (power B.carrier m)).inv ≫
        (B.action n ▷ power B.carrier m)) := by
  have hc : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.convolutionAction hP H B n ▷ H.carrier) ≫
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.convolutionEvaluation H.carrier B.carrier =
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.convolutionAssembly (hP.diagonalComponent n) (H.coaction n)
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.convolutionPowerEvaluation H.carrier B.carrier n) (B.action n) := by
    rw [← _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.convolutionEvaluation_uncurry, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.convolutionAction_uncurry]
    rfl
  have hhead : ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.convolutionAction hP H B n ▷ power (homComplex A H.carrier B.carrier) m) ▷
        power H.carrier (m + 1)) ≫ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.convolutionPowerEvaluation H.carrier B.carrier (m + 1) =
      tensorμ (P.arity n ⊗ power (homComplex A H.carrier B.carrier) n)
          (power (homComplex A H.carrier B.carrier) m) H.carrier (power H.carrier m) ≫
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.convolutionAssembly (hP.diagonalComponent n) (H.coaction n)
            (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.convolutionPowerEvaluation H.carrier B.carrier n) (B.action n) ⊗ₘ
          _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.convolutionPowerEvaluation H.carrier B.carrier m) := by
    change _ ≫ (tensorμ _ _ _ _ ≫ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.convolutionEvaluation H.carrier B.carrier ⊗ₘ
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.convolutionPowerEvaluation H.carrier B.carrier m)) = _
    change (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.convolutionAction hP H B n ▷ _ ▷ (H.carrier ⊗ power H.carrier m)) ≫
      tensorμ _ _ _ _ ≫ _ = _
    rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.evaluation_head, hc]
  rw [hhead]
  convert _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.convolutionAssembly_tensorRight (hP.diagonalComponent n)
    (H.coaction n) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.convolutionPowerEvaluation H.carrier B.carrier n) (B.action n)
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.convolutionPowerEvaluation H.carrier B.carrier m) using 1 <;> rfl

end Operad

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads
