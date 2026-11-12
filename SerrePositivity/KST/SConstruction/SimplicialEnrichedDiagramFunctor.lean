module
public import SerrePositivity.KST.SConstruction.SimplicialDiagramEnrichment

/-! # 全高次比較の単体的図式から実図式値豊穣関手へ
概要：各段の豊穣作用と全ての面退化を、一つの実図式値豊穣関手に束ねる。
方針：全パラメータ自然性で標準 end へ持ち上げ、射影で元の単位・合成を回収する。
規約：図式全体の Hom を頂点の族へ弱めない。使われ方：厳密 dg 入力に対する実 S•。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed Limits SSet
open SerrePositivity.InfinityCategories

local instance simplicialDiagramFunctorBase_enrichedCategory :
    EnrichedCategory SSet.{u} SSet.{u} :=
  MonoidalClosed.enrichedCategorySelf SSet.{u}
local instance simplicialDiagramFunctorBase_enrichedOrdinaryCategory :
    EnrichedOrdinaryCategory SSet.{u} SSet.{u} :=
  MonoidalClosed.enrichedOrdinaryCategorySelf SSet.{u}

variable {C : Type v} [Category.{u} C] [SimplicialCategory C]
  (D : SimplicialObject (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.QuasicategoryEnrichedFunctorCategory C))

/-- 同じ一対象での図式の評価を、元の単体的単体集合として読む。 -/
def simplicialEnrichedDiagramValue (X : C) : SimplicialObject SSet.{u} :=
  D ⋙ quasicategoryEnrichedEvaluationFunctor X ⋙ _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.quasicategoryObjectForget

/-- 同じ全パラメータの段ごとの作用を、図式全体の標準豊穣 Hom に持ち上げる。 -/
def simplicialEnrichedDiagramHom (X Y : C) :
    (X ⟶[SSet.{u}] Y) ⟶
      Enriched.FunctorCategory.enrichedHom SSet
        (simplicialEnrichedDiagramValue D X) (simplicialEnrichedDiagramValue D Y) :=
  end_.lift (fun n => (D.obj n).map X Y) (by
    intro i j f
    change (D.obj i).map X Y ≫
      eHomWhiskerLeft SSet.{u} ((D.obj i).obj X).obj ((D.map f).val Y) =
        (D.obj j).map X Y ≫
          eHomWhiskerRight SSet.{u} ((D.map f).val X) ((D.obj j).obj Y).obj
    erw [enrichedOrdinaryCategorySelf_eHomWhiskerLeft,
      enrichedOrdinaryCategorySelf_eHomWhiskerRight]
    exact quasicategoryEnrichedComparison_internal_naturality (D.map f) X Y)

/-- 元の全図式の Hom の各射影は、同じ段の元の全パラメータ作用。 -/
lemma simplicialEnrichedDiagramHom_projection (X Y : C) (n : SimplexCategoryᵒᵖ) :
    simplicialEnrichedDiagramHom D X Y ≫ Enriched.FunctorCategory.enrichedHomπ SSet.{u}
      (simplicialEnrichedDiagramValue D X) (simplicialEnrichedDiagramValue D Y) n =
        (D.obj n).map X Y := end_.lift_π _ _ _

/-- 元の全高次入力を、同じ単体的図式全体へ送る厳密豊穣関手。 -/
def simplicialEnrichedDiagramFunctor : EnrichedFunctor SSet.{u} C SimplicialSSetDiagram.{u} where
  obj X := ⟨simplicialEnrichedDiagramValue D X⟩
  map := simplicialEnrichedDiagramHom D
  map_id X := by
    apply end_.hom_ext
    intro n
    erw [Category.assoc, simplicialEnrichedDiagramHom_projection,
      Enriched.FunctorCategory.enrichedId_π]
    exact (D.obj n).map_id X
  map_comp X Y Z := by
    apply end_.hom_ext
    intro n
    erw [Category.assoc, simplicialEnrichedDiagramHom_projection, Category.assoc,
      Enriched.FunctorCategory.enrichedComp_π]
    erw [← Category.assoc, tensorHom_comp_tensorHom]
    erw [simplicialEnrichedDiagramHom_projection, simplicialEnrichedDiagramHom_projection]
    exact (D.obj n).map_comp X Y Z

/-- 図式全体への豊穣作用は、標準の内側の射影で同じ段の全入力族を回収する。 -/
lemma simplicialEnrichedDiagramFunctor_projection (X Y : C) (n : SimplexCategoryᵒᵖ) :
    (simplicialEnrichedDiagramFunctor D).map X Y ≫ simplicialSSetDiagramProjection
      ((simplicialEnrichedDiagramFunctor D).obj X) ((simplicialEnrichedDiagramFunctor D).obj Y) n =
        (D.obj n).map X Y := simplicialEnrichedDiagramHom_projection D X Y n

end SerrePositivity.KST.SConstruction
