module
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGMultiSCoreDiagram
public import SerrePositivity.KST.SConstruction.SimplicialEnrichedDiagramFunctor
public import SerrePositivity.KST.SConstruction.MultiSOneComparison

/-! # 一次方向を固定した元の core 図式の厳密豊穣関手
概要：先頭次数を 1 に固定した元の core 図式を、全 native 入力族とともに保持する。
方針：元の多単体図式を同じ添字で制限して標準 end に束ねる。
規約：元の通常射を全段で回収する。使われ方：一次方向の商の標準点つき豊穣化。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A]

/-- 先頭次数を 1 に固定して残りを対角に取る、元の全 core 比較の図式。 -/
def presentedPerfectDGOneDirectionCoreDiagram (r : ℕ) :
    SimplicialObject (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.QuasicategoryEnrichedFunctorCategory (PerfDGInput.{u, v} A)) :=
  (multiIndexDiagonal r ⋙ oneDirectionIndex r) ⋙
    presentedPerfectDGMultiSCoreEnrichedDiagram A (r + 1)

/-- 同じ一次方向の元の図式全体へ送る、全 native 入力を保つ厳密豊穣関手。 -/
def presentedPerfectDGOneDirectionObjectEnrichedFunctor (r : ℕ) :
    EnrichedFunctor SSet.{max (u + 1) v} (PerfDGInput.{u, v} A)
      SimplicialSSetDiagram.{max (u + 1) v} :=
  simplicialEnrichedDiagramFunctor (presentedPerfectDGOneDirectionCoreDiagram A r)

/-- 実図式は、元の一次方向を固定した同じ反復 core 図式。 -/
lemma presentedPerfectDGOneDirectionObjectEnrichedFunctor_obj (r : ℕ)
    (C : PerfDGInput.{u, v} A) :
    ((presentedPerfectDGOneDirectionObjectEnrichedFunctor A r).obj C).diagram =
      multiIndexDiagonal r ⋙ oneDirectionIndex r ⋙ multiCoreSConstruction (r + 1)
        (stableCategoryModel (presentedPerfectDGStableCategory A C)) := rfl

/-- 各 Hom 射影は、元の同じ多次数の全 native core 作用を回収する。 -/
lemma presentedPerfectDGOneDirectionObjectEnrichedFunctor_projection (r : ℕ)
    (C D : PerfDGInput.{u, v} A) (n : SimplexCategoryᵒᵖ) :
    (presentedPerfectDGOneDirectionObjectEnrichedFunctor A r).map C D ≫
      simplicialSSetDiagramProjection
        ((presentedPerfectDGOneDirectionObjectEnrichedFunctor A r).obj C)
        ((presentedPerfectDGOneDirectionObjectEnrichedFunctor A r).obj D) n =
      ((presentedPerfectDGMultiSCoreEnrichedDiagram A (r + 1)).obj
        ((oneDirectionIndex r).obj (fun _ => n))).map C D :=
  simplicialEnrichedDiagramFunctor_projection
    (presentedPerfectDGOneDirectionCoreDiagram A r) C D n

/-- 元の通常 dg 射が与える、同じ一次方向の core 図式の自然変換。 -/
def presentedPerfectDGOneDirectionObjectMap (r : ℕ)
    {C D : PerfDGInput.{u, v} A} (F : C ⟶ D) :
    (presentedPerfectDGOneDirectionObjectEnrichedFunctor A r).obj C ⟶
      (presentedPerfectDGOneDirectionObjectEnrichedFunctor A r).obj D :=
  Functor.whiskerLeft (multiIndexDiagonal r ⋙ oneDirectionIndex r)
    ((multiCoreSConstructionFunctor (r + 1)).map
      ⟨(presentedPerfectDGExactMap A F).hom,
        preservesCofiberData_of_isExactFunctor (presentedPerfectDGExactMap A F).hom⟩)

/-- 通常の厳密 dg 射では、同じ元の core 自然変換を全段で厳密に回収する。 -/
lemma presentedPerfectDGOneDirectionObjectEnrichedFunctor_hom (r : ℕ)
    {C D : PerfDGInput.{u, v} A} (F : C ⟶ D) :
    eHomEquiv SSet.{max (u + 1) v} F ≫
      (presentedPerfectDGOneDirectionObjectEnrichedFunctor A r).map C D =
        eHomEquiv SSet.{max (u + 1) v} (presentedPerfectDGOneDirectionObjectMap A r F) := by
  apply simplicialSSetDiagramHom_ext
  intro n
  rw [Category.assoc, presentedPerfectDGOneDirectionObjectEnrichedFunctor_projection,
    simplicialSSetDiagramHomEquiv_projection]
  exact presentedPerfectDGMultiSCoreEnrichedDiagram_hom A (r + 1)
    ((oneDirectionIndex r).obj (fun _ => n)) F

end SerrePositivity.KST.SConstruction
