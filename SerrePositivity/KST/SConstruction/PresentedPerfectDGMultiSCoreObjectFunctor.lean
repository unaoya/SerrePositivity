module
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGMultiSCoreDiagram
public import SerrePositivity.KST.SConstruction.SimplicialEnrichedDiagramFunctor

/-! # 全 native 入力を持つ反復 core S• の対角図式
概要：全多単体作用を保持した反復 core 図式を、元の対角図式の内側の Hom へ束ねる。
方針：既存の全方向対角で前合成し、標準 end による厳密豊穣関手を適用する。
規約：内部対角の Kan 性は主張しない。使われ方：元の反復実現への全パラメータ接続。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A]

/-- 全 S 方向を同じ次数へ制限した、元の反復 core S• の厳密豊穣図式。 -/
def presentedPerfectDGMultiSCoreDiagonalDiagram (r : ℕ) :
    SimplicialObject (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.QuasicategoryEnrichedFunctorCategory (PerfDGInput.{u, v} A)) :=
  multiIndexDiagonal r ⋙ presentedPerfectDGMultiSCoreEnrichedDiagram A r

/-- 全 native 入力を反復 core S• 対角図式全体へ送る厳密豊穣関手。 -/
def presentedPerfectDGMultiSCoreObjectEnrichedFunctor (r : ℕ) :
    EnrichedFunctor SSet.{max (u + 1) v} (PerfDGInput.{u, v} A)
      SimplicialSSetDiagram.{max (u + 1) v} :=
  simplicialEnrichedDiagramFunctor (presentedPerfectDGMultiSCoreDiagonalDiagram A r)

/-- 豊穣作用の実値は、元の同じ全反復 core S• の対角図式。 -/
lemma presentedPerfectDGMultiSCoreObjectEnrichedFunctor_obj (r : ℕ)
    (C : PerfDGInput.{u, v} A) :
    ((presentedPerfectDGMultiSCoreObjectEnrichedFunctor A r).obj C).diagram =
      multiIndexDiagonal r ⋙ multiCoreSConstruction r
        (stableCategoryModel (presentedPerfectDGStableCategory A C)) := rfl

/-- 図式全体の各 Hom 射影は、元の同じ多次数の全 native 入力族を回収する。 -/
lemma presentedPerfectDGMultiSCoreObjectEnrichedFunctor_projection (r : ℕ)
    (C D : PerfDGInput.{u, v} A) (n : SimplexCategoryᵒᵖ) :
    (presentedPerfectDGMultiSCoreObjectEnrichedFunctor A r).map C D ≫
      simplicialSSetDiagramProjection
        ((presentedPerfectDGMultiSCoreObjectEnrichedFunctor A r).obj C)
        ((presentedPerfectDGMultiSCoreObjectEnrichedFunctor A r).obj D) n =
      ((presentedPerfectDGMultiSCoreEnrichedDiagram A r).obj (fun _ => n)).map C D :=
  simplicialEnrichedDiagramFunctor_projection
    (presentedPerfectDGMultiSCoreDiagonalDiagram A r) C D n

/-- 通常 dg 射による、元の同じ反復 core S• 対角図式の自然変換。 -/
def presentedPerfectDGMultiSCoreObjectMap (r : ℕ)
    {C D : PerfDGInput.{u, v} A} (F : C ⟶ D) :
    (presentedPerfectDGMultiSCoreObjectEnrichedFunctor A r).obj C ⟶
      (presentedPerfectDGMultiSCoreObjectEnrichedFunctor A r).obj D :=
  Functor.whiskerLeft (multiIndexDiagonal r)
    ((multiCoreSConstructionFunctor r).map
      ⟨(presentedPerfectDGExactMap A F).hom,
        preservesCofiberData_of_isExactFunctor (presentedPerfectDGExactMap A F).hom⟩)

/-- 元の通常 dg 入力射では、同じ元の反復 core 自然変換を全段で回収する。 -/
lemma presentedPerfectDGMultiSCoreObjectEnrichedFunctor_hom (r : ℕ)
    {C D : PerfDGInput.{u, v} A} (F : C ⟶ D) :
    eHomEquiv SSet.{max (u + 1) v} F ≫
      (presentedPerfectDGMultiSCoreObjectEnrichedFunctor A r).map C D =
        eHomEquiv SSet.{max (u + 1) v} (presentedPerfectDGMultiSCoreObjectMap A r F) := by
  apply simplicialSSetDiagramHom_ext
  intro n
  rw [Category.assoc, presentedPerfectDGMultiSCoreObjectEnrichedFunctor_projection,
    simplicialSSetDiagramHomEquiv_projection]
  exact presentedPerfectDGMultiSCoreEnrichedDiagram_hom A r (fun _ => n) F

/-- 内部の単体方向も対角に取ると、同じ元の反復実現の実値を回収する。 -/
lemma presentedPerfectDGMultiSCoreObjectEnrichedFunctor_realization (r : ℕ)
    (C : PerfDGInput.{u, v} A) :
    Functor.diag SimplexCategoryᵒᵖ ⋙ Functor.uncurry.obj
      ((presentedPerfectDGMultiSCoreObjectEnrichedFunctor A r).obj C).diagram =
        multiDiagonalCoreSConstruction r
          (stableCategoryModel (presentedPerfectDGStableCategory A C)) := rfl

/-- 通常 dg 射の対角像も、同じ元の反復実現の射を厳密に回収する。 -/
lemma presentedPerfectDGMultiSCoreObjectMap_realization (r : ℕ)
    {C D : PerfDGInput.{u, v} A} (F : C ⟶ D) :
    Functor.whiskerLeft (Functor.diag SimplexCategoryᵒᵖ)
      (Functor.uncurry.map (show
        ((presentedPerfectDGMultiSCoreObjectEnrichedFunctor A r).obj C).diagram ⟶
          ((presentedPerfectDGMultiSCoreObjectEnrichedFunctor A r).obj D).diagram from
            presentedPerfectDGMultiSCoreObjectMap A r F)) =
      (multiRealizationFunctor r).map
        ⟨(presentedPerfectDGExactMap A F).hom,
          preservesCofiberData_of_isExactFunctor (presentedPerfectDGExactMap A F).hom⟩ := rfl

end SerrePositivity.KST.SConstruction
