module

public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.NormalizedMooreSplitMono
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.NormalizedCochainCofibrant
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.ExtendSplitMono
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.SplitMonoCokernelProjective

/-!
# 単体集合の単射の実正規化像は射影 cofibration

概要：元の正規化鎖関手は全ての単射を実射影 cofibration へ送る。
方針：次数別の実分裂と射影 cokernel を零延長し、全障害消滅で持ち上げる。
規約：有限性・可縮性・標数の仮定を課さない。
使われ方：正規化単体の境界の Reedy cofibrancy。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.ComplexLimits
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.HomologicalComplex _root_.CochainComplex
open _root_.SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A]

lemma normalizedCochainMap_degreewise_isSplitMono {X Y : SSet.{0}}
    (f : X ⟶ Y) [Mono f] (n : ℤ) :
    IsSplitMono (((_root_.SerrePositivity.EInfinity.BarrattEccles.normalizedFunctor A).map f).f n) := by
  change IsSplitMono ((extendMap _ ComplexShape.embeddingDownNat).f n)
  exact _root_.SerrePositivity.ComplexLimits.extendMap_degreewise_isSplitMono _ (_root_.SerrePositivity.ComplexLimits.normalizedChainMap_isSplitMono A f) _ n

lemma normalizedMonomorphism_cofibration {X Y : SSet.{0}} (f : X ⟶ Y) [Mono f] :
    (_root_.SerrePositivity.ProjectiveModel.projectiveGeneratingCofibrations A).rlp.llp ((_root_.SerrePositivity.EInfinity.BarrattEccles.normalizedFunctor A).map f) := by
  let i := (_root_.SerrePositivity.EInfinity.BarrattEccles.normalizedFunctor A).map f
  have hs (n : ℤ) : IsSplitMono (i.f n) := _root_.SerrePositivity.ComplexLimits.normalizedCochainMap_degreewise_isSplitMono A f n
  have : Mono i := mono_of_mono_f i (fun n => by have := hs n; infer_instance)
  have (n : ℤ) : Projective ((cokernel i).X n) := by
    have := hs n
    have := _root_.SerrePositivity.ComplexLimits.normalizedCochain_projective A Y n
    have h : Projective (cokernel (i.f n)) := _root_.SerrePositivity.ComplexLimits.splitMono_cokernel_projective (i.f n)
    exact Projective.of_iso (asIso (cokernelComparison i (HomologicalComplex.eval _ _ n))) h
  have : CochainComplex.IsStrictlyLE ((_root_.SerrePositivity.EInfinity.BarrattEccles.normalizedFunctor A).obj Y) 0 := by
    change CochainComplex.IsStrictlyLE
      (((AlgebraicTopology.normalizedMooreComplex (ModuleCat A)).obj
        ((_root_.SerrePositivity.EInfinity.BarrattEccles.linearization A).obj Y)).extend ComplexShape.embeddingDownNat) 0
    infer_instance
  exact _root_.SerrePositivity.ComplexLimits.projectiveCofibration_of_boundedAboveCokernel i 0

end SerrePositivity.ComplexLimits
