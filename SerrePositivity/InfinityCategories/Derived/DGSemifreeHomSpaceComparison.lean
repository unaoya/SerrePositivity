module
public import SerrePositivity.InfinityCategories.Derived.DGModuleOutputResolutionSpaceIso
public import SerrePositivity.InfinityCategories.Derived.DGSemifreeHomSpaceAugmentation
/-!
概要：固定入力の D(R) 値 Hom の基礎空間を、元の同じ全 Hom の空間値関手と比較する。
方針：同じ実 augmentation の全関手同型を実入力へ制限し、反変側は実反対 nerve を経る。
規約：全単体族の比較同型。元の導来圏の F1 Hom 関手との同定は別工程。
使われ方：β5 の D(R) 値 Hom と空間値 Hom の自然な比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
/-- 同じ実 augmentation による、固定始域の全空間値関手の比較同型。 -/
def dgSemifreeDerivedHomTargetSpaceIso (P : SemifreeDGModules R D) :
    FunctorIso (dgSemifreeDerivedHomTargetSpaceInfinity R D P)
      (dgSemifreeHomTargetSpaceInfinity R D P) := by
  have e := FunctorIso.precomp
    (dgModuleOutputResolutionSpaceComparisonIso R (SemifreeDGModules R D)
      (dgSemifreeHomTargetModuleDG R D P))
    ((SSet.uliftFunctor.{max (u + 1) v + 1, max (u + 1) v}).map
      (dgNerve.map (dgUniverseLiftUp.{u, max (u + 1) v, u + 1} R
        (SemifreeDGModules R D))))
  have h1 : dgNerve.map
      (dgUniverseLiftUp.{u, max (u + 1) v, u + 1} R (SemifreeDGModules R D)) ≫
        dgNerve.map (dgModuleOutputOriginalLift R (SemifreeDGModules R D) PUnit.{1}
          (dgSemifreeHomTargetModuleDG R D P)) =
      dgSemifreeHomTargetModuleInfinity R D P := by
    rw [← dgNerve.map_comp, dgModuleOutputOriginalLift_up]
    rfl
  simp only [← Category.assoc, ← Functor.map_comp] at e
  rw [h1] at e
  simpa only [dgSemifreeDerivedHomTargetSpaceInfinity, dgHomDerivedSpaceInfinity,
    dgSemifreeDerivedHomTargetInfinity, dgHomModuleInclusionInfinity,
    dgSemifreeHomTargetSpaceInfinity, Functor.map_comp, Category.assoc,
    dgHomUnderlyingSpaceInfinity,
    dgHomModuleUnitVertex, dgHomModuleUnit, dgHomModuleNerve] using e
/-- 同じ実 augmentation による、dg 反対模型上の固定終域 Hom の全関手比較同型。 -/
def dgSemifreeDerivedHomSourceSpaceIso (P : SemifreeDGModules R D) :
    FunctorIso (((SSet.uliftFunctor.{max (u + 1) v + 1, max (u + 1) v}).map
      (dgSemifreeDerivedHomSourceDGopInfinity R D P) ≫ dgHomDerivedSpaceInfinity R D))
      (((SSet.uliftFunctor.{max (u + 1) v + 1, max (u + 1) v}).map
      (dgSemifreeHomSourceModuleInfinity R D P) ≫ dgHomUnderlyingSpaceInfinity R D)) := by
  have e := FunctorIso.precomp
    (dgModuleOutputResolutionSpaceComparisonIso R (SemifreeDGModules R D)ᵒᵖ
      (dgSemifreeHomSourceModuleDG R D P))
    ((SSet.uliftFunctor.{max (u + 1) v + 1, max (u + 1) v}).map
      (dgNerve.map (dgUniverseLiftUp.{u, max (u + 1) v, u + 1} R
        (SemifreeDGModules R D)ᵒᵖ)))
  have h1 : dgNerve.map
      (dgUniverseLiftUp.{u, max (u + 1) v, u + 1} R (SemifreeDGModules R D)ᵒᵖ) ≫
        dgNerve.map (dgModuleOutputOriginalLift R (SemifreeDGModules R D)ᵒᵖ PUnit.{1}
          (dgSemifreeHomSourceModuleDG R D P)) =
      dgSemifreeHomSourceModuleInfinity R D P := by
    rw [← dgNerve.map_comp, dgModuleOutputOriginalLift_up]
    rfl
  simp only [← Category.assoc, ← Functor.map_comp] at e
  rw [h1] at e
  simpa only [dgHomDerivedSpaceInfinity,
    dgSemifreeDerivedHomSourceDGopInfinity, dgHomModuleInclusionInfinity,
    Functor.map_comp, Category.assoc, dgHomUnderlyingSpaceInfinity,
    dgHomModuleUnitVertex, dgHomModuleUnit, dgHomModuleNerve] using e
/-- 実反対 ∞ 圏上の D(R) 値 Hom と元の全 Hom の、全空間値関手の比較同型。 -/
def dgSemifreeDerivedHomContravariantSpaceIso (Q : SemifreeDGModules R D) :
    FunctorIso (dgSemifreeDerivedHomContravariantSpaceInfinity R D Q)
      (dgSemifreeHomContravariantSpaceInfinity R D Q) := by
  have e := FunctorIso.precomp (dgSemifreeDerivedHomSourceSpaceIso R D Q)
    ((SSet.uliftFunctor.{max (u + 1) v + 1, max (u + 1) v}).map
      (dgNerveOppositeIso R (SemifreeDGModules R D)).hom)
  simpa only [dgSemifreeDerivedHomContravariantSpaceInfinity,
    dgSemifreeHomContravariantSpaceInfinity, dgSemifreeDerivedContravariantHomInfinity,
    dgSemifreeHomContravariantModuleInfinity, Functor.map_comp, Category.assoc] using e
end SerrePositivity.InfinityCategories
