module

public import SerrePositivity.InfinityCategories.F1.CocartesianTwoHornNativeTarget
public import SerrePositivity.InfinityCategories.F1.CocartesianOneBoundaryOriginal
public import SerrePositivity.InfinityCategories.F1.CocartesianHornBoundaryExtensionKan
public import SerrePositivity.InfinityCategories.F1.CocartesianNativeRestrictionMap

/-!
概要：実際の二次内ホーンから、欠けた面の同じ共有境界への両側の制限。
方針：元の底上の共有境界包含に直接制限する。
規約：有限二単体の元の fibrations と同じ共有境界を保持する。
使われ方：二次元境界のホーン側の指定自然性と厳密化。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped Simplicial
namespace SerrePositivity.InfinityCategories
variable (p q : CocartesianFibrationCategory (nerve (ULift.{u} (Fin 3))))
local notation "σ" => Iso.hom (stdSimplex.isoNerve 2)
local notation "P" => cocartesianStrictTransportCoherentDiagram p.val.hom
local notation "Q" => cocartesianStrictTransportCoherentDiagram q.val.hom

/-- 元の二次内ホーンの native Hom の、同じ共有境界への制限。 -/
def cocartesianTwoHornSharedNativeRestriction :=
  cocartesianPullbackNativeLiftPre p.val.hom q.val.hom (HornBoundaryOver.toHorn 1 1 σ)

/-- 同じ分類先のホーン Hom の、同じ共有境界への制限。 -/
def cocartesianTwoHornSharedTargetRestriction :=
  intervalDiagramOverPre P Q (uliftOverMorphism (HornBoundaryOver.toHorn 1 1 σ))

/-- 元の大域 native 制限をホーンと共有境界で二回行うと、同じ直接制限。 -/
lemma cocartesianTwoHornSharedNativeRestriction_original :
    cocartesianPullbackNativeLiftRestriction p.val.hom q.val.hom (cocartesianFiniteHornOver 2 1) ≫
      cocartesianTwoHornSharedNativeRestriction p q =
    cocartesianPullbackNativeLiftRestriction p.val.hom q.val.hom (HornBoundaryOver.shared 1 1 σ) :=
  cocartesianPullbackNativeLiftRestriction_naturality p.val.hom q.val.hom
    (HornBoundaryOver.toHorn 1 1 σ)

/-- 同じ分類先でも、二回の制限は元の共有境界への直接制限。 -/
lemma cocartesianTwoHornSharedTargetRestriction_original :
    intervalDiagramRestriction ((SSet.uliftFunctor.{u + 1, u}).map
      (cocartesianFiniteHornOver 2 1).hom) P Q ≫ cocartesianTwoHornSharedTargetRestriction p q =
    intervalDiagramRestriction ((SSet.uliftFunctor.{u + 1, u}).map
      (HornBoundaryOver.shared 1 1 σ).hom) P Q :=
  intervalDiagramOverPre_restriction P Q (uliftOverMorphism (HornBoundaryOver.toHorn 1 1 σ))

/-- 同じ native 制限は Kan fibration。 -/
instance cocartesianTwoHornSharedNativeRestriction_fibration :
    Fibration (cocartesianTwoHornSharedNativeRestriction p q) :=
  cocartesianPullbackNativeLiftPre_fibration p.val.hom q.val.hom (HornBoundaryOver.toHorn 1 1 σ)

/-- 同じ分類先の制限も Kan fibration。 -/
instance cocartesianTwoHornSharedTargetRestriction_fibration :
    Fibration (cocartesianTwoHornSharedTargetRestriction p q) := by
  have : Mono (uliftOverMorphism.{u, u + 1} (HornBoundaryOver.toHorn 1 1 σ)).left :=
    SimplicialModel.UniverseLift.mono_map (HornBoundaryOver.toHorn 1 1 σ).left
  exact intervalDiagramOverPre_fibration P Q (uliftOverMorphism (HornBoundaryOver.toHorn 1 1 σ))

end SerrePositivity.InfinityCategories
