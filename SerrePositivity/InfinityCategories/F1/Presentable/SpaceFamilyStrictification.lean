module

public import SerrePositivity.InfinityCategories.Core.Equivalence
public import SerrePositivity.InfinityCategories.F1.Categories.CatInfinity
public import SerrePositivity.InfinityCategories.F1.Categories.KanDiagramCoherentNerve
public import SerrePositivity.InfinityCategories.F1.FunctorCategories.FunctorSpaceCurrying
public import SerrePositivity.InfinityCategories.Core.Ind.NerveProductSwapIso
public import SerrePositivity.InfinityCategories.HomotopyLimits.Presentable.SpaceDiagramStrictification

/-!
概要：coherent な空間値図式の族を、一つの積添字上の strict Kan 図式へ同時に移す。
方針：元の族を uncurry し、積の nerve の同型を通じて一度だけ strict 化する。
規約：族全体の関手同型と、任意の通常の制限上の比較を同じデータから回収する。
使われ方：filtered 添字と錐形状を同時に保持した、native な極限交換への移送。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.F2.Presentable
open Ind
variable {I J : Type u} [SmallCategory I] [SmallCategory J]
  (F : (SSet.uliftFunctor.{u + 1, u}).obj (nerve J) ⟶
    (ihom ((SSet.uliftFunctor.{u + 1, u}).obj (nerve I))).obj SpaceInfinity.{u})

/-- 元の族の共同図式を、同じ積圏の nerve 上に厳密に読み替える。 -/
def spaceFamilyJointDiagram :
    (SSet.uliftFunctor.{u + 1, u}).obj (nerve (J × I)) ⟶ SpaceInfinity.{u} :=
  (uliftNerveProductSwapIso J I).hom ≫ uncurry F

/-- 元の共同図式を一度だけ復元した、同じ積圏上の strict Kan 図式。 -/
def spaceFamilyStrictification : J × I ⥤ KanObject.{u} :=
  spaceDiagramStrictification (spaceFamilyJointDiagram F)

/-- 同じ strict 共同図式を元の族の型へ戻す。 -/
def spaceFamilyStrictRealization :
    (SSet.uliftFunctor.{u + 1, u}).obj (nerve J) ⟶
      (ihom ((SSet.uliftFunctor.{u + 1, u}).obj (nerve I))).obj SpaceInfinity.{u} :=
  curry ((uliftNerveProductSwapIso J I).inv ≫
    kanDiagramCoherentNerve (spaceFamilyStrictification F))

/-- 各値で選んだ比較ではなく、元の族全体を回収する一つの関手同型。 -/
def spaceFamilyStrictificationIso : FunctorIso (spaceFamilyStrictRealization F) F := by
  have h := ((spaceDiagramStrictificationIso (spaceFamilyJointDiagram F)).precomp
    (uliftNerveProductSwapIso J I).inv).curry
  simpa only [spaceFamilyStrictRealization, spaceFamilyStrictification, spaceFamilyJointDiagram,
    ← Category.assoc, Iso.inv_hom_id, Category.id_comp, curry_uncurry] using h

/-- 任意の通常の制限の比較も同じ共同同型から得られ、制限した strict 図式自体を保持する。 -/
def spaceFamilyStrictificationRestrictIso {L : Type u} [SmallCategory L] (H : L ⥤ J × I) :
    FunctorIso (kanDiagramCoherentNerve (H ⋙ spaceFamilyStrictification F))
      ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap H) ≫ spaceFamilyJointDiagram F) := by
  have h := (spaceDiagramStrictificationIso (spaceFamilyJointDiagram F)).precomp
    ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap H))
  rw [kanDiagramCoherentNerve_precomp] at h
  exact h

end SerrePositivity.InfinityCategories.F2.Presentable
