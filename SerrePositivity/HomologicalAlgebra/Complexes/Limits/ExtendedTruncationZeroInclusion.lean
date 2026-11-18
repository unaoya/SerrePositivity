module

public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.ExtendTruncationHomInclusion

/-!
# 元の延長 smart 切断包含と Hom 回収の零次数

概要：元の切断 Hom の零次数像を、同じ包含を通して元の複体射の零次数へ戻す。
方針：元の全射の回収式を零次数に評価し、延長の同じ項同型を相殺する。
規約：元の shape 等式・項同型・包含を保つ。
使われ方：実 Γ の零次数像と元の複体射の直接評価。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.ComplexLimits
open _root_.CategoryTheory _root_.HomologicalComplex
open _root_.SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A]

def truncationExtendedZeroInclusion
    (e : (ComplexShape.down ℕ).Embedding (ComplexShape.up ℤ))
    (he : e = ComplexShape.embeddingUpIntLE 0) (hz : e.f 0 = (0 : ℤ)) (H : Complex A) :
    (H.truncLE' (ComplexShape.embeddingUpIntLE 0)).X 0 ⟶ H.X 0 :=
  ((H.truncLE' (ComplexShape.embeddingUpIntLE 0)).extendXIso e hz).inv ≫
    (_root_.SerrePositivity.ComplexLimits.truncationExtendedInclusionOfShape A e he H).f 0

lemma extendTruncationHomEquivOfShape_zero
    (e : (ComplexShape.down ℕ).Embedding (ComplexShape.up ℤ))
    (he : e = ComplexShape.embeddingUpIntLE 0) (hz : e.f 0 = (0 : ℤ))
    (L : ChainComplex (ModuleCat.{u} A) ℕ) (H : Complex A) (f : L.extend e ⟶ H) :
    (_root_.SerrePositivity.ComplexLimits.extendTruncationHomEquivOfShape A e he L H f).f 0 ≫
      _root_.SerrePositivity.ComplexLimits.truncationExtendedZeroInclusion A e he hz H = (L.extendXIso e hz).inv ≫ f.f 0 := by
  have h := congrArg (fun g => g.f 0)
    (_root_.SerrePositivity.ComplexLimits.extendTruncationHomEquivOfShape_inclusion A e he L H f)
  change (extendMap _ e).f 0 ≫ (_root_.SerrePositivity.ComplexLimits.truncationExtendedInclusionOfShape A e he H).f 0 = f.f 0 at h
  rw [extendMap_f _ _ hz] at h
  have h' := congrArg (fun g => (L.extendXIso e hz).inv ≫ g) h
  simpa only [_root_.SerrePositivity.ComplexLimits.truncationExtendedZeroInclusion, Category.assoc, Iso.inv_hom_id_assoc] using h'

end SerrePositivity.ComplexLimits
