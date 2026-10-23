module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.OneBoundaryLocalNaturality
public import SerrePositivity.InfinityCategories.F1.Cocartesian.CellAttachmentFibrations

/-!
概要：任意の一単体上の全局所 Hom の、元の境界への両側の制限と Kan 性。
方針：単射な標準境界包含に元の制限の充填性を適用する。
規約：底への一単体写像の単射性を要求しない。
使われ方：任意の一単体の両端固定 Hom 比較。
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
variable {C : Type u} [Category.{u} C]
  (σ : (Δ[1] : SSet.{u}) ⟶ nerve C) (p q : CocartesianFibrationCategory (nerve C))

/-- 分類先の同じ宇宙持ち上げ済み反変図式の全ての値は Kan。 -/
instance cocartesianIntervalLiftOverFunctor_obj_kan (z : Over (nerve C)) : KanComplex
    (((uliftOverFunctor (nerve C)).op ⋙
      intervalDiagramOverFunctor (cocartesianStrictTransportCoherentDiagram p.val.hom)
        (cocartesianStrictTransportCoherentDiagram q.val.hom)).obj (Opposite.op z)) :=
  inferInstanceAs (KanComplex (intervalMappingSpace
    (functorVertex ((SSet.uliftFunctor.{u + 1, u}).map z.hom ≫
      cocartesianStrictTransportCoherentDiagram p.val.hom))
    (functorVertex ((SSet.uliftFunctor.{u + 1, u}).map z.hom ≫
      cocartesianStrictTransportCoherentDiagram q.val.hom))))

/-- 元の一単体上の全 native Hom の同じ境界への制限。 -/
def cocartesianOneBoundaryLocalSourceRestriction :=
  ((cocartesianPullbackNativeCoreFunctor p.val.hom q.val.hom) ⋙
    SSet.uliftFunctor.{u + 1, u}).map (boundarySimplexOverMap 0 σ).op

/-- 元の一単体上の分類先 Hom の同じ境界への制限。 -/
def cocartesianOneBoundaryLocalTargetRestriction :=
  ((uliftOverFunctor (nerve C)).op ⋙
    intervalDiagramOverFunctor (cocartesianStrictTransportCoherentDiagram p.val.hom)
      (cocartesianStrictTransportCoherentDiagram q.val.hom)).map (boundarySimplexOverMap 0 σ).op

/-- 元の native Hom の同じ境界制限は Kan fibration。 -/
instance cocartesianOneBoundaryLocalSourceRestriction_fibration :
    Fibration (cocartesianOneBoundaryLocalSourceRestriction σ p q) := by
  have : Mono (boundarySimplexOverMap 0 σ).left := inferInstanceAs (Mono (boundary 1).ι)
  exact cocartesianPullbackNativeLiftPre_fibration p.val.hom q.val.hom (boundarySimplexOverMap 0 σ)

/-- 元の分類先 Hom の同じ境界制限も Kan fibration。 -/
instance cocartesianOneBoundaryLocalTargetRestriction_fibration :
    Fibration (cocartesianOneBoundaryLocalTargetRestriction σ p q) := by
  have : Mono (boundarySimplexOverMap 0 σ).left := inferInstanceAs (Mono (boundary 1).ι)
  have : Mono (uliftOverMorphism.{u, u + 1} (boundarySimplexOverMap 0 σ)).left :=
    SimplicialModel.UniverseLift.mono_map (boundarySimplexOverMap 0 σ).left
  exact intervalDiagramOverPre_fibration _ _ (uliftOverMorphism (boundarySimplexOverMap 0 σ))

end SerrePositivity.InfinityCategories
