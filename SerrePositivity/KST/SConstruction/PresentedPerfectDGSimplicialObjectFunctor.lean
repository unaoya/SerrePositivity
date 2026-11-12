module
public import SerrePositivity.KST.SConstruction.SimplicialEnrichedDiagramFunctor
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGSimplicialEnrichedFunctor

/-! # 元の全 dg 入力から実 S• 全体への厳密豊穣関手
概要：元の全 native Kan dg 入力を、単体的図式全体の標準豊穣 Hom へ送る。
方針：全高次比較の実 S• 図式を標準 end に束ね、元の各段と通常射を回収する。
規約：core・反復・実現・BF は後続。使われ方：図式全体を保持する連結 K の入力。
-/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed Limits SSet Enriched.FunctorCategory
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories

local instance perfectDGSimplicialBase_enrichedCategory :
    EnrichedCategory SSet.{w} SSet.{w} :=
  MonoidalClosed.enrichedCategorySelf SSet.{w}
local instance perfectDGSimplicialBase_enrichedOrdinaryCategory :
    EnrichedOrdinaryCategory SSet.{w} SSet.{w} :=
  MonoidalClosed.enrichedOrdinaryCategorySelf SSet.{w}

variable (A : Type u) [CommRing A]

/-- 元の全 native Kan 入力族を、同じ実 S• 全体へ送る厳密単体的豊穣関手。 -/
def presentedPerfectDGSimplicialObjectEnrichedFunctor :
    EnrichedFunctor SSet.{max (u + 1) v} (PerfDGInput.{u, v} A)
      SimplicialSSetDiagram.{max (u + 1) v} :=
  simplicialEnrichedDiagramFunctor (presentedPerfectDGSimplicialEnrichedFunctor A)

/-- 図式全体の実値の各段は、元の同じ全 gapped S_n Perf。 -/
lemma presentedPerfectDGSimplicialObjectEnrichedFunctor_obj
    (C : PerfDGInput.{u, v} A) (n : SimplexCategoryᵒᵖ) :
    ((presentedPerfectDGSimplicialObjectEnrichedFunctor A).obj C).diagram.obj n =
      sConstruction n.unop.len (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A (PresentedPerfectDGObject A C)) := rfl

/-- 図式全体の実値の全ての面退化は、元の同じ添字制限。 -/
lemma presentedPerfectDGSimplicialObjectEnrichedFunctor_obj_map
    (C : PerfDGInput.{u, v} A) {n m : SimplexCategoryᵒᵖ} (f : n ⟶ m) :
    ((presentedPerfectDGSimplicialObjectEnrichedFunctor A).obj C).diagram.map f =
      sMap (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A (PresentedPerfectDGObject A C)) f.unop.toOrderHom := rfl

/-- 図式全体の Hom を射影すると、同じ元の段の全 native Kan 入力族を回収する。 -/
lemma presentedPerfectDGSimplicialObjectEnrichedFunctor_projection
    (C D : PerfDGInput.{u, v} A) (n : SimplexCategoryᵒᵖ) :
    (presentedPerfectDGSimplicialObjectEnrichedFunctor A).map C D ≫
      enrichedHomπ SSet.{max (u + 1) v}
      ((presentedPerfectDGSimplicialObjectEnrichedFunctor A).obj C).diagram
      ((presentedPerfectDGSimplicialObjectEnrichedFunctor A).obj D).diagram n =
        ((presentedPerfectDGSimplicialEnrichedFunctor A).obj n).map C D :=
  simplicialEnrichedDiagramHom_projection
    (presentedPerfectDGSimplicialEnrichedFunctor.{u, v} A) C D n

/-- 元の厳密 dg 射による全 cofiber 型 S_n 後合成を、同じ実 S• 間の自然変換に束ねる。 -/
def presentedPerfectDGSimplicialObjectMap {C D : PerfDGInput.{u, v} A} (F : C ⟶ D) :
    (presentedPerfectDGSimplicialObjectEnrichedFunctor A).obj C ⟶
      (presentedPerfectDGSimplicialObjectEnrichedFunctor A).obj D where
  app n := (sExactMap n.unop.len (presentedPerfectDGExactMap A F)).hom
  naturality _i _j f := (sPostcompCofiber_sMap (presentedPerfectDGExactMap A F).hom
    (preservesCofiberData_of_isExactFunctor (presentedPerfectDGExactMap A F).hom)
      f.unop.toOrderHom).symm

/-- 元の通常の dg 入力射では、同じ元の実 S• 自然変換の豊穣表示を回収する。 -/
lemma presentedPerfectDGSimplicialObjectEnrichedFunctor_hom
    {C D : PerfDGInput.{u, v} A} (F : C ⟶ D) :
    eHomEquiv SSet.{max (u + 1) v} F ≫
      (presentedPerfectDGSimplicialObjectEnrichedFunctor A).map C D =
        eHomEquiv SSet.{max (u + 1) v} (presentedPerfectDGSimplicialObjectMap A F) := by
  apply end_.hom_ext
  intro n
  erw [Category.assoc, presentedPerfectDGSimplicialObjectEnrichedFunctor_projection,
    homEquiv_apply_π]
  exact presentedPerfectDGSimplicialEnrichedFunctor_hom A n F

end SerrePositivity.KST.SConstruction
