module

public import SerrePositivity.InfinityCategories.F2.Ind.StrictRightFibrationFiberCocone
public import SerrePositivity.InfinityCategories.F2.Ind.FilteredKanCocone

/-!
概要：strict right fibration 余極限の元の fiber 余錐は SpaceInfinity の余極限。
方針：元の fiber 図式と余錐を Kan 対象に束ね、filtered Kan 余極限の判定を適用する。
規約：元の余錐の全脚と高次の整合性を保った native な余極限性。
使われ方：coherent な前層余錐への点ごとの比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
open HomotopyLimits
variable {B : SSet.{u}} {I : Type u} [SmallCategory I]

/-- 元の各 right fiber を Kan 対象として束ねた同じ図式。 -/
def rightFibrationFiberKanDiagram (F : I ⥤ RightFibrationObject B) (b : B _⦋0⦌) :
    I ⥤ KanObject.{u} where
  obj i := ⟨vertexFiber (F.obj i).val.hom b, vertexFiber_kanComplex _ _⟩
  map f := (rightFibrationFiberDiagram F b).map f
  map_id i := (rightFibrationFiberDiagram F b).map_id i
  map_comp f g := (rightFibrationFiberDiagram F b).map_comp f g

/-- Kan 図式の台は元の同じ fiber 図式。 -/
lemma rightFibrationFiberKanDiagram_forget (F : I ⥤ RightFibrationObject B) (b : B _⦋0⦌) :
    rightFibrationFiberKanDiagram F b ⋙ kanObjectForget = rightFibrationFiberDiagram F b := rfl

variable [IsFiltered I]

/-- 同じ strict 余極限の実際の fiber を Kan 対象に束ねる。 -/
def strictRightFibrationColimitFiberKanObject (F : I ⥤ RightFibrationObject B)
    (b : B _⦋0⦌) : KanObject.{u} :=
  ⟨vertexFiber (strictRightFibrationColimitProjection F) b, vertexFiber_kanComplex _ _⟩

/-- 元の全空間の余極限の脚から得た同じ Kan 余錐。 -/
def strictRightFibrationFiberKanCocone (F : I ⥤ RightFibrationObject B)
    (b : B _⦋0⦌) : Cocone (rightFibrationFiberKanDiagram F b) where
  pt := strictRightFibrationColimitFiberKanObject F b
  ι := { app i := (strictRightFibrationFiberColimitCocone F b).ι.app i
         naturality _ _ f := (strictRightFibrationFiberColimitCocone F b).ι.naturality f }

/-- Kan 余錐の台は同じ実際の fiber 余錐。 -/
lemma strictRightFibrationFiberKanCocone_forget (F : I ⥤ RightFibrationObject B)
    (b : B _⦋0⦌) : kanObjectForget.mapCocone (strictRightFibrationFiberKanCocone F b) =
      strictRightFibrationFiberColimitCocone F b := rfl

/-- 同じ元の Kan 余錐の native な余極限性。 -/
lemma strictRightFibrationFiberKanCocone_isColimit (F : I ⥤ RightFibrationObject B)
    (b : B _⦋0⦌) : IsColimitCone (strictNativeCocone (strictRightFibrationFiberKanCocone F b)) :=
  strictNativeCocone_isColimit_of_filtered_forget _
    (strictRightFibrationFiberColimitCocone_isColimit F b)

/-- 元の fiber 図式の標準の coherent 表示上の同じ native 余錐。 -/
def strictRightFibrationFiberNativeCocone (F : I ⥤ RightFibrationObject B)
    (b : B _⦋0⦌) : JoinCocone (kanDiagramCoherentNerve (rightFibrationFiberKanDiagram F b)) :=
  coherentCoconeOfDiagramEq (strictCoherentDiagram_eq_kanDiagram _)
    (strictNativeCocone (strictRightFibrationFiberKanCocone F b))

/-- 元の fiber 図式の同じ native 余錐は SpaceInfinity の余極限。 -/
lemma strictRightFibrationFiberNativeCocone_isColimit (F : I ⥤ RightFibrationObject B)
    (b : B _⦋0⦌) : IsColimitCone (strictRightFibrationFiberNativeCocone F b) :=
  (coherentCoconeOfDiagramEq_isColimit_iff _ _).mp
    (strictRightFibrationFiberKanCocone_isColimit F b)

/-- 同じ native 余極限の頂点は元の strict 余極限射影の実際の fiber。 -/
lemma strictRightFibrationFiberNativeCocone_vertex (F : I ⥤ RightFibrationObject B)
    (b : B _⦋0⦌) : (strictRightFibrationFiberNativeCocone F b).vertex =
      spaceInfinityVertex (strictRightFibrationColimitFiberKanObject F b) := by
  rw [strictRightFibrationFiberNativeCocone, coherentCoconeOfDiagramEq_vertex,
    strictNativeCocone_vertex]
  exact (spaceInfinityVertex_eq_coherent _).symm

end SerrePositivity.InfinityCategories.F2.Ind
