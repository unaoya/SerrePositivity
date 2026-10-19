module
public import SerrePositivity.InfinityCategories.Derived.DGModuleFiberCofiberComparisonProjection
public import SerrePositivity.InfinityCategories.Derived.DGModuleConePushout
public import SerrePositivity.InfinityCategories.Derived.PushoutComparison

/-! # dg 加群の標準 fiber 四角形の押し出し性

概要：標準 fiber 四角形は全 Hom end の dg 加群 nerve 内で押し出しでもある。
方針：降下射の同値性を実 coslice 比較辺へ反映し、cone の余極限性を移送する。
規約：安定性を仮定しない。使われ方：β3 の零角の双カルテジアン判定。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable {M N : ModuleCategory A D}

/-- 標準 cone 余錐から元の fiber 余錐への実 coslice 比較辺は可逆。 -/
lemma dgModuleFiberCofiberComparisonSliceEdge_isInvertible (f : M ⟶ N) :
    IsInvertibleEdge (X := sliceUnder (pushoutSpan
      (dgModuleConeSquare A D (dgModuleFiberProjection A D f))))
      (dgModuleFiberCofiberComparisonSliceEdge A D f) := by
  have he := dgModuleFiberCofiberDesc_isInvertible A D f
  have hp := (isInvertibleEdge_congr (X := dgModuleNerve A D)
    (dgModuleFiberCofiberComparisonSliceEdge_projection A D f)).mpr he
  exact leftFibration_reflects_invertibleEdge
    (sliceUnderProjection (pushoutSpan
      (dgModuleConeSquare A D (dgModuleFiberProjection A D f))))
    (dgModuleFiberCofiberComparisonSliceEdge A D f) hp

/-- 標準 fiber 四角形は dg 加群 nerve の押し出しでもある。 -/
lemma dgModuleFiberSquare_isPushout (f : M ⟶ N) :
    IsPushoutSquare (dgModuleFiberSquare A D f) := by
  have := dgModuleFiberCofiberComparisonSliceEdge_isInvertible A D f
  have hc : IsColimitCone (dgModuleFiberCofiberTargetCocone A D f) :=
    (dgModuleConeCocone_isColimit A D (dgModuleFiberProjection A D f)).of_vertexIso
      (asIso (SSet.Truncated.HomotopyCategory.homMk
        (dgModuleFiberCofiberComparisonSliceEdge A D f)))
  exact (rebaseCocone_isColimit_iff (dgModuleFiberCofiberComparison_span A D f)
    (pushoutCocone (dgModuleFiberSquare A D f))).mp hc

end SerrePositivity.InfinityCategories
