module

public import SerrePositivity.EInfinity.Operad.ConvolutionOperations
public import SerrePositivity.EInfinity.Operad.ConvolutionUnitEvaluation
public import SerrePositivity.EInfinity.Operad.ConvolutionAssemblyTensor
public import SerrePositivity.EInfinity.Operad.ConvolutionEvaluationAppend

/-!
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

namespace SerrePositivity.EInfinity

open CategoryTheory MonoidalCategory
open SerrePositivity.DifferentialGraded SerrePositivity.TensorPowers

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

variable {A : Type u} [CommRing A] {P : Operad A}

attribute [local irreducible] HomologicalComplex.monoidalCategoryStruct
attribute [local implicit_reducible] TensorPowers.power
attribute [local implicit_reducible] SerrePositivity.SymmetricSequence
  SerrePositivity.SymmetricSequence.level

/-- 概要：先頭の convolution と後方の評価は余代入・反復評価・代入の図式になる（BF §3.1）。
方針：先頭の転置の評価を戻し、独立な後方の評価を組み立ての各段へ通す。
規約：入力の関数と評価点を前半・後半の二ブロックのまま明示する。
使われ方：先頭位置の部分合成則で入力代入と出力余代入を比較する。 -/
lemma convolutionAction_firstBlock_evaluation (hP : Hopf P) (H : P.Coalgebra)
    (B : P.Algebra) (n m : ℕ) :
    ((α_ (P.arity n) (power (homComplex A H.carrier B.carrier) n)
        (power (homComplex A H.carrier B.carrier) m)).inv ▷ power H.carrier (m + 1)) ≫
      ((convolutionAction hP H B n ▷ power (homComplex A H.carrier B.carrier) m) ▷
        power H.carrier (m + 1)) ≫ convolutionPowerEvaluation H.carrier B.carrier (m + 1) =
    convolutionAssembly (hP.diagonalComponent n)
      ((α_ (P.arity n) H.carrier (power H.carrier m)).inv ≫
        (H.coaction n ▷ power H.carrier m))
      (tensorμ (power (homComplex A H.carrier B.carrier) n)
          (power (homComplex A H.carrier B.carrier) m) (power H.carrier n) (power H.carrier m) ≫
        (convolutionPowerEvaluation H.carrier B.carrier n ⊗ₘ
          convolutionPowerEvaluation H.carrier B.carrier m))
      ((α_ (P.arity n) (power B.carrier n) (power B.carrier m)).inv ≫
        (B.action n ▷ power B.carrier m)) := by
  have hc : (convolutionAction hP H B n ▷ H.carrier) ≫
      convolutionEvaluation H.carrier B.carrier =
      convolutionAssembly (hP.diagonalComponent n) (H.coaction n)
        (convolutionPowerEvaluation H.carrier B.carrier n) (B.action n) := by
    rw [← convolutionEvaluation_uncurry, convolutionAction_uncurry]
    rfl
  have hhead : ((convolutionAction hP H B n ▷ power (homComplex A H.carrier B.carrier) m) ▷
        power H.carrier (m + 1)) ≫ convolutionPowerEvaluation H.carrier B.carrier (m + 1) =
      tensorμ (P.arity n ⊗ power (homComplex A H.carrier B.carrier) n)
          (power (homComplex A H.carrier B.carrier) m) H.carrier (power H.carrier m) ≫
        (convolutionAssembly (hP.diagonalComponent n) (H.coaction n)
            (convolutionPowerEvaluation H.carrier B.carrier n) (B.action n) ⊗ₘ
          convolutionPowerEvaluation H.carrier B.carrier m) := by
    change _ ≫ (tensorμ _ _ _ _ ≫ (convolutionEvaluation H.carrier B.carrier ⊗ₘ
      convolutionPowerEvaluation H.carrier B.carrier m)) = _
    change (convolutionAction hP H B n ▷ _ ▷ (H.carrier ⊗ power H.carrier m)) ≫
      tensorμ _ _ _ _ ≫ _ = _
    rw [evaluation_head, hc]
  rw [hhead]
  convert convolutionAssembly_tensorRight (hP.diagonalComponent n)
    (H.coaction n) (convolutionPowerEvaluation H.carrier B.carrier n) (B.action n)
    (convolutionPowerEvaluation H.carrier B.carrier m) using 1 <;> rfl

end Operad

end SerrePositivity.EInfinity
