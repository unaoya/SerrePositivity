module

public import SerrePositivity.InfinityCategories.F2.Ind.IndLeftKanCommaIso
public import SerrePositivity.InfinityCategories.F2.Ind.ElementsYonedaSliceEquivalence

/-!
概要：指定 Indκ 頂点の元の小さい元の圏を、左 Kan 局所添字の同値な模型へ移す。
方針：元の Yoneda comma 比較と全部分圏の添字同型の逆を合成する。
規約：元の C への射影と、任意の元の図式の制限を厳密に保つ。
使われ方：小さい κ-filtered 余極限の存在から局所 Kan 余極限を得る。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
variable (κ : Cardinal.{u}) {C : SSet.{u}} [Quasicategory C] (v : (IndInfinity κ C) _⦋0⦌)

/-- 元の左 Kan 局所添字の射影は right fibration。 -/
instance indLeftKanProjection_rightFibration :
    RightFibration (leftKanProjection (indYoneda κ C) v) :=
  ⟨rightFibrations.pullback_fst _ _ (RightFibration.mem (p :=
    sliceOverProjection (SSet.yonedaEquiv.symm v)))⟩

/-- 同じ元の左 Kan 局所添字は quasicategory。 -/
instance indLeftKanShape_quasicategory : Quasicategory (leftKanShape (indYoneda κ C) v) :=
  quasicategory_of_innerFibration (leftKanProjection (indYoneda κ C) v)

/-- 同じ元の小さい元の圏から、同じ Indκ 頂点の左 Kan 局所添字への比較。 -/
def indElementsLeftKanComparison :
    (SSet.uliftFunctor.{u + 1, u}).obj (smallRightUnstraightening (indVertexPresheaf κ v)) ⟶
      leftKanShape (indYoneda κ C) v :=
  presheafElementsYonedaSliceComparison (indVertexPresheaf κ v) ≫ (indLeftKanCommaIso κ v).inv

/-- 同じ局所添字への比較自体が同値。 -/
lemma indElementsLeftKanComparison_isQCatEquivalence :
    IsQCatEquivalence (indElementsLeftKanComparison κ v) :=
  (presheafElementsYonedaSliceComparison_isQCatEquivalence (indVertexPresheaf κ v)).comp
    (qCatEquivalenceOfIso (indLeftKanCommaIso κ v).symm).isQCatEquivalence

/-- 同じ比較は、元の小さい元の圏の射影を厳密に保つ。 -/
lemma indElementsLeftKanComparison_projection :
    indElementsLeftKanComparison κ v ≫ leftKanProjection (indYoneda κ C) v =
      (SSet.uliftFunctor.{u + 1, u}).map
        (smallRightUnstraighteningProjection (indVertexPresheaf κ v)) := by
  rw [indElementsLeftKanComparison, Category.assoc, indLeftKanCommaIso_inv_projection,
    presheafElementsYonedaSliceComparison_projection]

/-- 任意の元の図式を同じ小さい模型へ制限すると、元の元の圏上の図式そのもの。 -/
lemma indElementsLeftKanComparison_diagram {D : SSet.{u + 1}}
    (F₀ : (SSet.uliftFunctor.{u + 1, u}).obj C ⟶ D) :
    indElementsLeftKanComparison κ v ≫ leftKanDiagram (indYoneda κ C) F₀ v =
      (SSet.uliftFunctor.{u + 1, u}).map
        (smallRightUnstraighteningProjection (indVertexPresheaf κ v)) ≫ F₀ := by
  rw [leftKanDiagram, ← Category.assoc, indElementsLeftKanComparison_projection]

end SerrePositivity.InfinityCategories.F2.Ind
