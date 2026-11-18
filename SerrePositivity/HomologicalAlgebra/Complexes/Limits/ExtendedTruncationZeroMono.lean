module

public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.ExtendedTruncationZeroInclusion
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.DoldKanZeroIso

/-!
# 元の延長切断の零次数包含の単射性

概要：同じ切断包含と実 Γ 零次数同型の合成は単射である。
方針：元の包含の零次数の単射性と同じ二つの項同型を使う。
規約：元の切断・延長・Γ 同型を保つ。
使われ方：元の Γ 零次数像を元の Hom 複体の値で分離する。
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

lemma truncationExtendedZeroInclusion_mono
    (e : (ComplexShape.down ℕ).Embedding (ComplexShape.up ℤ))
    (he : e = ComplexShape.embeddingUpIntLE 0) (hz : e.f 0 = (0 : ℤ)) (H : Complex A) :
    Mono (_root_.SerrePositivity.ComplexLimits.truncationExtendedZeroInclusion A e he hz H) := by
  have : Mono ((_root_.SerrePositivity.ComplexLimits.truncationExtendedInclusionOfShape A e he H).f 0) := by
    subst e
    have : Mono ((H.ιTruncLE 0).f 0) := by
      change Mono ((HomologicalComplex.ιTruncLE H (ComplexShape.embeddingUpIntLE 0)).f 0)
      infer_instance
    have : IsIso ((H.truncLEIso (ComplexShape.embeddingUpIntLE 0)).inv.f 0) := by
      change IsIso ((HomologicalComplex.eval (ModuleCat A) (.up ℤ) 0).map
        (H.truncLEIso (ComplexShape.embeddingUpIntLE 0)).inv)
      infer_instance
    change Mono ((H.truncLEIso (ComplexShape.embeddingUpIntLE 0)).inv.f 0 ≫
      (H.ιTruncLE 0).f 0)
    infer_instance
  dsimp only [_root_.SerrePositivity.ComplexLimits.truncationExtendedZeroInclusion]
  infer_instance

lemma gammaDegreeZero_raw_injective (H : Complex A) :
    Function.Injective (fun x => _root_.SerrePositivity.ComplexLimits.truncationExtendedZeroInclusion A ComplexShape.embeddingDownNat
      _root_.SerrePositivity.ComplexLimits.embeddingDownNat_eq_upIntLE_zero rfl H
      ((_root_.SerrePositivity.ComplexLimits.gammaDegreeZeroIso (H.truncLE' (ComplexShape.embeddingUpIntLE 0))).hom x)) := by
  have := _root_.SerrePositivity.ComplexLimits.truncationExtendedZeroInclusion_mono A ComplexShape.embeddingDownNat
    _root_.SerrePositivity.ComplexLimits.embeddingDownNat_eq_upIntLE_zero rfl H
  exact (ModuleCat.mono_iff_injective
    ((_root_.SerrePositivity.ComplexLimits.gammaDegreeZeroIso (H.truncLE' (ComplexShape.embeddingUpIntLE 0))).hom ≫
      _root_.SerrePositivity.ComplexLimits.truncationExtendedZeroInclusion A ComplexShape.embeddingDownNat
        _root_.SerrePositivity.ComplexLimits.embeddingDownNat_eq_upIntLE_zero rfl H)).mp inferInstance

end SerrePositivity.ComplexLimits
