module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.StandardSimplexNaturality
public import SerrePositivity.InfinityCategories.F1.Cocartesian.OneHornComparison

/-!
概要：標準一単体の全局所比較を、同じホーン側の端点へ制限する指定自然性。
方針：同じ標準点の自然性を、元のホーン表示同型で運ぶ。
規約：大域から制限された像に限定しない。
使われ方：一次元境界の二端点で指定同型を対にする。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories
variable {C : Type u} [Category.{u} C] (i : Fin 2)
  (σ : (Δ[1] : SSet.{u}) ⟶ nerve C) (p q : CocartesianFibrationCategory (nerve C))
local notation "N" => (cocartesianPullbackNativeCoreFunctor p.val.hom q.val.hom) ⋙
  SSet.uliftFunctor
local notation "T" => Functor.op (uliftOverFunctor (nerve C)) ⋙
  intervalDiagramOverFunctor (cocartesianStrictTransportCoherentDiagram p.val.hom)
    (cocartesianStrictTransportCoherentDiagram q.val.hom)

local instance (z : (Over (nerve C))ᵒᵖ) : Quasicategory ((T).obj z) :=
  inferInstanceAs (Quasicategory (intervalMappingSpace
    (functorVertex ((SSet.uliftFunctor.{u + 1, u}).map z.unop.hom ≫
      cocartesianStrictTransportCoherentDiagram p.val.hom))
    (functorVertex ((SSet.uliftFunctor.{u + 1, u}).map z.unop.hom ≫
      cocartesianStrictTransportCoherentDiagram q.val.hom))))

/-- 同じホーンの、元の標準一単体への底上の包含。 -/
def hornOneSimplexOverMap : HornBoundaryOver.horn 0 i σ ⟶ Over.mk σ :=
  Over.homMk (horn 1 i).ι rfl

/-- 標準点から元の一単体への同じ底上の写像。 -/
def hornOnePointSimplexOverMap : Over.mk (hornOnePointMap i σ) ⟶ Over.mk σ :=
  Over.homMk ((hornOnePointIso i).hom ≫ (horn 1 i).ι) (Category.assoc _ _ _)

/-- 元のホーン表示同型と両包含の正方形は厳密に可換。 -/
lemma hornOnePointSimplexOverMap_comp :
    (hornOnePointOverIso i σ).hom ≫ hornOneSimplexOverMap i σ =
      hornOnePointSimplexOverMap i σ := by
  apply Over.OverMorphism.ext
  rfl

/-- 全局所 Hom の同じ一単体比較は、ホーン側の端点への直接制限に自然。 -/
def cocartesianOneHornHomComparison_localNaturalityIso :
    FunctorIso
      ((N).map (hornOneSimplexOverMap i σ).op ≫ cocartesianOneHornHomComparison i σ p q)
      (cocartesianStandardSimplexHomComparison σ p q ≫
        (T).map (hornOneSimplexOverMap i σ).op) := by
  have hc : (hornOnePointOverIso i σ).inv ≫ hornOnePointSimplexOverMap i σ =
      hornOneSimplexOverMap i σ ≫ (Iso.refl (Over.mk σ)).hom := by
    rw [← hornOnePointSimplexOverMap_comp]
    simp only [Iso.refl_hom, Category.comp_id, Iso.inv_hom_id_assoc]
  have h := contravariantComparisonIso (N) (T) (hornOnePointOverIso i σ).symm
    (Iso.refl (Over.mk σ)) (hornOneSimplexOverMap i σ) (hornOnePointSimplexOverMap i σ) hc
    (cocartesianStandardSimplexHomComparison (hornOnePointMap i σ) p q)
    (cocartesianStandardSimplexHomComparison σ p q)
    (cocartesianStandardSimplexHomComparison_overNaturalityIso
      ((hornOnePointIso i).hom ≫ (horn 1 i).ι) σ p q (hornOnePointMap i σ)
      (Category.assoc _ _ _))
  apply F2.functorIsoOfEq h
  · rw [cocartesianOneHornHomComparison, cocartesianOneHornSourceIso_hom,
      cocartesianOneHornTargetIso_hom]
    rfl
  · simp only [Iso.refl_inv, Iso.refl_hom, op_id]
    rw [(N).map_id, (T).map_id, Category.id_comp, Category.comp_id]

end SerrePositivity.InfinityCategories
