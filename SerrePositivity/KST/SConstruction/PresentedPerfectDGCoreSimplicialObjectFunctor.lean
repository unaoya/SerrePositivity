module
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGCoreSimplicialEnrichedFunctor
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGSimplicialObjectFunctor

/-! # 元の全 dg 入力から実 core S• 全体への厳密豊穣関手
概要：全 native Kan 入力族を、同じ実 core S• 全体の内側の標準 end へ送る。
方針：全高次比較を保つ実 core 図式を束ね、各段と元の通常射を回収する。
規約：反復・実現・BF は後続。使われ方：連結 K の全パラメータ化の入力。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A]

/-- 全 native Kan dg 入力族を同じ実 core S• 全体へ送る厳密豊穣関手。 -/
def presentedPerfectDGCoreSimplicialObjectEnrichedFunctor :
    EnrichedFunctor SSet.{max (u + 1) v} (PerfDGInput.{u, v} A)
      SimplicialSSetDiagram.{max (u + 1) v} :=
  simplicialEnrichedDiagramFunctor (presentedPerfectDGCoreSimplicialEnrichedFunctor A)

/-- 図式全体の値の各段は、同じ元の全 gapped S_n Perf の core。 -/
lemma presentedPerfectDGCoreSimplicialObjectEnrichedFunctor_obj
    (C : PerfDGInput.{u, v} A) (n : SimplexCategoryᵒᵖ) :
    ((presentedPerfectDGCoreSimplicialObjectEnrichedFunctor A).obj C).diagram.obj n =
      coreSConstruction n.unop.len (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A (PresentedPerfectDGObject A C)) := rfl

/-- 図式全体の全ての面退化は、同じ元の添字制限の core 射。 -/
lemma presentedPerfectDGCoreSimplicialObjectEnrichedFunctor_obj_map
    (C : PerfDGInput.{u, v} A) {n m : SimplexCategoryᵒᵖ} (f : n ⟶ m) :
    ((presentedPerfectDGCoreSimplicialObjectEnrichedFunctor A).obj C).diagram.map f =
      coreSMap (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A (PresentedPerfectDGObject A C)) f.unop.toOrderHom := rfl

/-- 図式全体の Hom の各射影は、同じ段の全 native Kan 入力族を回収する。 -/
lemma presentedPerfectDGCoreSimplicialObjectEnrichedFunctor_projection
    (C D : PerfDGInput.{u, v} A) (n : SimplexCategoryᵒᵖ) :
    (presentedPerfectDGCoreSimplicialObjectEnrichedFunctor A).map C D ≫
      simplicialSSetDiagramProjection
        ((presentedPerfectDGCoreSimplicialObjectEnrichedFunctor A).obj C)
        ((presentedPerfectDGCoreSimplicialObjectEnrichedFunctor A).obj D) n =
      ((presentedPerfectDGCoreSimplicialEnrichedFunctor A).obj n).map C D :=
  simplicialEnrichedDiagramFunctor_projection
    (presentedPerfectDGCoreSimplicialEnrichedFunctor A) C D n

/-- 元の通常 dg 射による S• 自然変換の、同じ実 core 自然変換。 -/
def presentedPerfectDGCoreSimplicialObjectMap {C D : PerfDGInput.{u, v} A} (F : C ⟶ D) :
    (presentedPerfectDGCoreSimplicialObjectEnrichedFunctor A).obj C ⟶
      (presentedPerfectDGCoreSimplicialObjectEnrichedFunctor A).obj D :=
  Functor.whiskerRight (show
    ((presentedPerfectDGSimplicialObjectEnrichedFunctor A).obj C).diagram ⟶
      ((presentedPerfectDGSimplicialObjectEnrichedFunctor A).obj D).diagram from
        presentedPerfectDGSimplicialObjectMap A F) _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreFunctor

/-- 通常 dg 入力射では、同じ元の core S• 自然変換の豊穣表示を回収する。 -/
lemma presentedPerfectDGCoreSimplicialObjectEnrichedFunctor_hom
    {C D : PerfDGInput.{u, v} A} (F : C ⟶ D) :
    eHomEquiv SSet.{max (u + 1) v} F ≫
      (presentedPerfectDGCoreSimplicialObjectEnrichedFunctor A).map C D =
        eHomEquiv SSet.{max (u + 1) v} (presentedPerfectDGCoreSimplicialObjectMap A F) := by
  apply simplicialSSetDiagramHom_ext
  intro n
  rw [Category.assoc, presentedPerfectDGCoreSimplicialObjectEnrichedFunctor_projection,
    simplicialSSetDiagramHomEquiv_projection]
  exact presentedPerfectDGCoreSimplicialEnrichedFunctor_hom A n F

end SerrePositivity.KST.SConstruction
