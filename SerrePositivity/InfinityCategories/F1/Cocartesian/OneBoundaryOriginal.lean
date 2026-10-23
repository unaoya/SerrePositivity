module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.OneBoundaryOriginalTarget
public import SerrePositivity.InfinityCategories.F1.FunctorCategories.PairedKanFunctorIso

/-!
概要：実際の一次元境界全体の比較を、元の大域の全 Hom 作用へ指定同型で戻す。
方針：両端の既存の指定同型を対にし、同じ target 積分解の逆で境界へ戻す。
規約：同じ比較写像と元の分類主写像を保持する。
使われ方：高次境界の比較と共有境界での整合性の初期値。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories
variable {C : Type u} [Category.{u} C] (i : Fin 2) (σ : (Δ[1] : SSet.{u}) ⟶ nerve C)
  (p q : CocartesianFibrationCategory (nerve C))
local notation "P" => cocartesianStrictTransportCoherentDiagram p.val.hom
local notation "Q" => cocartesianStrictTransportCoherentDiagram q.val.hom

local instance (z : Over ((SSet.uliftFunctor.{u + 1, u}).obj (nerve C))) :
    KanComplex ((intervalDiagramOverFunctor P Q).obj (Opposite.op z)) :=
  inferInstanceAs (KanComplex (intervalMappingSpace
    (functorVertex (z.hom ≫ P)) (functorVertex (z.hom ≫ Q))))

/-- 同じ一次元境界比較は、元の全 Hom 作用の境界制限と指定関手同型で可換。 -/
def cocartesianOneBoundaryHomComparison_originalIso :
    FunctorIso
      (cocartesianPullbackNativeLiftRestriction p.val.hom q.val.hom
        (HornBoundaryOver.apex 0 σ) ≫ cocartesianOneBoundaryHomComparison i σ p q)
      (cocartesianStraighteningHomInterval p q ≫ intervalDiagramRestriction
        ((SSet.uliftFunctor.{u + 1, u}).map (HornBoundaryOver.apex 0 σ).hom) P Q) := by
  have h : FunctorIso
      ((cocartesianPullbackNativeLiftRestriction p.val.hom q.val.hom
        (HornBoundaryOver.apex 0 σ) ≫ cocartesianOneBoundaryHomComparison i σ p q) ≫
          (cocartesianOneBoundaryIntervalProductIso i σ P Q).hom)
      ((cocartesianStraighteningHomInterval p q ≫ intervalDiagramRestriction
        ((SSet.uliftFunctor.{u + 1, u}).map (HornBoundaryOver.apex 0 σ).hom) P Q) ≫
          (cocartesianOneBoundaryIntervalProductIso i σ P Q).hom) := by
    apply F2.functorIsoOfEq (pairedKanFunctorIso
      (cocartesianStandardSimplexHomComparison_originalIso (stdSimplex.δ i ≫ σ) p q)
      (cocartesianOneHornHomComparison_originalIso i σ p q))
    · simpa only [Over.mk_hom, HornBoundaryOver.face, intervalDiagramOverFunctor] using
        (cocartesianOneBoundaryHomComparison_originalSourceProduct i σ p q).symm
    · simpa only [cocartesianOneBoundaryOriginalFaceAction,
        cocartesianOneBoundaryOriginalHornAction, Over.mk_hom, HornBoundaryOver.face,
        intervalDiagramOverFunctor] using
        (cocartesianOneBoundaryHomComparison_originalTargetProduct i σ p q).symm
  apply F2.functorIsoOfEq
    (h.postcomp (cocartesianOneBoundaryIntervalProductIso i σ P Q).inv)
  · rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  · rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]

end SerrePositivity.InfinityCategories
