module

public import SerrePositivity.EInfinity.ComplexLimits.SemifreeResolutionWeak
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGClosedRoofRefinements

/-!
# 元の通常複体圏から既存 D(R) への実写像

概要：同じ複体と鎖写像を閉零圏へ移し、既存の半自由出力分解へ送る。
方針：標準の豊穣通常圏の同値と元の閉辺の式を使う。
規約：元の複体の cofibrancy を要求せず、元の準同型辺を反転する。
使われ方：CAlg_R の元の通常忘却の ∞ 関手化。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.ComplexLimits
open SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded SSet

open scoped Simplicial
variable (A : Type u) [CommRing A]

def complexToClosed : Complex A ⥤ ClosedCategory A (Complex A) :=
  ForgetEnrichment.equivInverse (Complex A) (Complex A)

lemma complexToClosed_map {X Y : Complex A} (f : X ⟶ Y) :
    (closedToComplex A).map ((complexToClosed A).map f) = f := by
  change (complexClosedHomEquiv A X Y) ((complexClosedHomEquiv A X Y).symm f) = f
  exact Equiv.apply_symm_apply _ _

def complexOrdinaryDerivedSource : nerve (Complex A) ⟶ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityCategory A :=
  nerveMap (complexToClosed A) ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.closedNerveInclusion A (Complex A) ≫
    complexSemifreeResolutionInfinity A

lemma complexOrdinaryDerivedSource_map_weak {X Y : Complex A} (f : X ⟶ Y)
    (hf : QuasiIso f) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge ((nerve.edgeMk f).map (complexOrdinaryDerivedSource A)).toTruncated := by
  let g := (complexToClosed A).map f
  have hg : QuasiIso ((closedToComplex A).map (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.edgeClosed (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge A (Complex A) g))) := by
    rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge_closed, complexToClosed_map]
    exact hf
  have h := complexSemifreeResolutionInfinity_invertsQuasiIso A
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge A (Complex A) g) hg
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr (e := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge A (Complex A) g).map
    ((truncation 2).map (complexSemifreeResolutionInfinity A)))
    (f := ((nerve.edgeMk f).map (complexOrdinaryDerivedSource A)).toTruncated) ?_).mp h
  change (complexSemifreeResolutionInfinity A).app (Opposite.op ⦋1⦌)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge A (Complex A) g).edge =
    (complexOrdinaryDerivedSource A).app (Opposite.op ⦋1⦌) (ComposableArrows.mk₁ f)
  simp only [complexOrdinaryDerivedSource, NatTrans.comp_app_apply, nerveMap_app_mk₁,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.closedNerveInclusion_mk₁]
  rfl

end SerrePositivity.EInfinity.ComplexLimits
