module
public import SerrePositivity.KST.Fibration.ZeroFunctorFullSMap
public import SerrePositivity.KST.Fibration.CoreFamilyDiagonalCylinder

/-!
概要：元の零値関手の全族を、全 S• 図式の豊穣 Hom と同じ実現円柱へ送る。
方針：全段の作用の自然性を標準 end にまとめ、既存の豊穣対角作用で実現する。
規約：元の全 S• と全パラメータを保持し、頂点ごとの比較で代用しない。
使われ方：指定 Verdier 二胞体による、商核上辺の全実現比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory MonoidalClosed SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction
open SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration

local instance : EnrichedCategory SSet.{u} SSet.{u} :=
  MonoidalClosed.enrichedCategorySelf SSet.{u}
local instance : EnrichedOrdinaryCategory SSet.{u} SSet.{u} :=
  MonoidalClosed.enrichedOrdinaryCategorySelf SSet.{u}

/-- 同じ全パラメータの関手族は、全段の面・退化制限に自然。 -/
theorem zeroFunctorFullSCoreFamily_reindex (A C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}) {m n : ℕ}
    (θ : Fin (m + 1) →o Fin (n + 1)) :
    zeroFunctorFullSCoreFamily A C n ≫
        (ihom (sConstruction n A.obj)).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreMap (sMap C.obj θ)) =
      zeroFunctorFullSCoreFamily A C m ≫
        (pre (sMap A.obj θ)).app (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore (sConstruction m C.obj) : SSet.{u}) := by
  apply uncurry_injective
  rw [uncurry_natural_right, uncurry_pre_app]
  simp only [zeroFunctorFullSCoreFamily, uncurry_curry]
  exact (zeroFunctorFullSCoreAction_reindex A C θ).symm

/-- 全段・全高次パラメータを保持する、同じ全 S• 図式の豊穣 Hom 族。 -/
def zeroFunctorFullSDiagramFamily (A C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}) :
    zeroFunctorLocus A C ⟶
      ((⟨simplicialSConstruction A.obj⟩ : SimplicialSSetDiagram.{u}) ⟶[SSet.{u}]
        (⟨simplicialSConstruction C.obj ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreFunctor⟩ : SimplicialSSetDiagram.{u})) :=
  end_.lift (fun n => zeroFunctorFullSCoreFamily A C n.unop.len) (by
    intro i j f
    change zeroFunctorFullSCoreFamily A C i.unop.len ≫
      eHomWhiskerLeft SSet (sConstruction i.unop.len A.obj)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreMap (sMap C.obj f.unop.toOrderHom)) =
      zeroFunctorFullSCoreFamily A C j.unop.len ≫
        eHomWhiskerRight SSet (sMap A.obj f.unop.toOrderHom)
          (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore (sConstruction j.unop.len C.obj) : SSet.{u})
    erw [enrichedOrdinaryCategorySelf_eHomWhiskerLeft,
      enrichedOrdinaryCategorySelf_eHomWhiskerRight]
    exact zeroFunctorFullSCoreFamily_reindex A C f.unop.toOrderHom)

/-- 元の図式 Hom の各射影は、同じ元の全零値関手族の段ごとの作用。 -/
theorem zeroFunctorFullSDiagramFamily_projection (A C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u})
    (n : SimplexCategoryᵒᵖ) :
    zeroFunctorFullSDiagramFamily A C ≫ simplicialSSetDiagramProjection _ _ n =
      zeroFunctorFullSCoreFamily A C n.unop.len := end_.lift_π _ _ _

/-- 元の全 S• 円柱の実現は、同じ全パラメータの豊穣対角作用そのもの。 -/
theorem zeroFunctorFullSDiagramFamily_diagonal (A C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}) :
    simplicialCylinderDiagonal _ _ (zeroFunctorLocus A C) (zeroFunctorFullSCoreNatTrans A C) =
      uncurry (zeroFunctorFullSDiagramFamily A C ≫
        simplicialSSetDiagramDiagonalEnrichedFunctor.map _ _) := by
  apply diagramCylinder_eq_diagonalFamily
  intro n
  erw [zeroFunctorFullSDiagramFamily_projection]
  exact (uncurry_curry _).symm

/-- 指定した元の零値関手を、同じ全パラメータ空間の実点として保持する。 -/
def zeroFunctorParameterPoint {A C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (F : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A C)
    (hF : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F.hom)) :
    (𝟙_ SSet.{u}) ⟶ zeroFunctorLocus A C :=
  (SSet.unitHomEquiv _).symm (fullSubcategoryVertex _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F.hom) hF)

/-- 完全関手空間への包含後も、指定した同じ完全関手の実点。 -/
theorem zeroFunctorParameterPoint_toExact {A C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (F : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A C)
    (hF : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F.hom)) :
    zeroFunctorParameterPoint F hF ≫ zeroFunctorLocusToExact A C = _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.exactHomEquiv F := by
  apply (cancel_mono (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.exactFunctors A C).ι).1
  rw [Category.assoc, zeroFunctorLocusToExact_inclusion, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.exactHomEquiv_ι]
  apply (SSet.unitHomEquiv _).injective
  rfl

/-- 全族を元の実点に制限すると、同じ全 S_n 後合成を回収する。 -/
theorem zeroFunctorFullSCoreFamily_fixed {A C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (F : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A C)
    (hF : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F.hom)) (n : ℕ) :
    zeroFunctorParameterPoint F hF ≫ zeroFunctorFullSCoreFamily A C n =
      curry' (zeroFunctorSCoreMap F hF n) := by
  apply uncurry_injective
  apply (cancel_mono (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore (sConstruction n C.obj)).ι).1
  rw [← uncurry_natural_right, Category.assoc, zeroFunctorFullSCoreFamily_ι,
    ← Category.assoc, zeroFunctorParameterPoint_toExact, sExactFamilyMap_fixed,
    ← uncurry_natural_right, curry'_ihom_map, zeroFunctorSCoreMap_ι]

/-- 図式全体の全族も、指定点では同じ元の全 S• 自然変換そのもの。 -/
theorem zeroFunctorFullSDiagramFamily_fixed {A C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (F : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A C)
    (hF : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F.hom)) :
    zeroFunctorParameterPoint F hF ≫ zeroFunctorFullSDiagramFamily A C =
      eHomEquiv SSet (show
        (⟨simplicialSConstruction A.obj⟩ : SimplicialSSetDiagram.{u}) ⟶
          ⟨simplicialSConstruction C.obj ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreFunctor⟩ from
            zeroFunctorFullSMap F hF) := by
  apply simplicialSSetDiagramHom_ext
  intro n
  rw [Category.assoc, zeroFunctorFullSDiagramFamily_projection,
    simplicialSSetDiagramHomEquiv_projection]
  exact zeroFunctorFullSCoreFamily_fixed F hF n.unop.len

end SerrePositivity.KST.Fibration
