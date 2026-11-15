module

public import SerrePositivity.InfinityCategories.Sheaves.Sheafification
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.DiscreteSpace
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.SpacePresentable

/-!
概要：集合値前層を、元の図式の coherent 表示で離散空間値前層へ送る。
方針：既存の setsToKan と kanDiagramCoherentNerve を用いる。
使われ方：HTT 5.5.6.28・6.2.2.7、Kerodon Corollary 5.6.0.6（Tag 028T）。
規約：空間値層化の存在は生成辺による実反射から得る。
-/

@[expose] public noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories
open SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects
namespace SerrePositivity.InfinityCategories.Sheaves
variable {C : Type u} [SmallCategory C]

/-- 集合値前層の同じ strict 図式の離散空間値表示。 -/
def discretePresheaf (P : Cᵒᵖ ⥤ Type u) : Presheaf C SpaceInfinity.{u} :=
  kanDiagramCoherentNerve (P ⋙ setsToKan)

/-- 離散前層は各頂点で元の集合の離散空間を取る。 -/
lemma discretePresheaf_vertex (P : Cᵒᵖ ⥤ Type u) (U : C) :
    (discretePresheaf P).app _ (ULift.up (nerveVertex (Opposite.op U))) =
      coherentNerveVertex (setsToKan.obj (P.obj (Opposite.op U))) :=
  kanDiagramCoherentNerve_vertex _ _

/-- 空間値層化は、元の篩辺族に対する Bousfield 反射として存在する。 -/
theorem sheafification_exists_spaces (J : GrothendieckTopology C) :
    Sheafification J SpaceInfinity.{u} :=
  sheafification_exists J space_isPresentable

end SerrePositivity.InfinityCategories.Sheaves
