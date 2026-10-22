module

public import SerrePositivity.InfinityCategories.F2.Ind.IndElementsLeftKanModel
public import SerrePositivity.InfinityCategories.F2.Ind.EquivalentRestrictionColimit

/-!
概要：小さい κ-filtered 余極限を持つ標的では、Indκ の元の Yoneda の局所 Kan 図式が余極限を持つ。
方針：元の小さい κ-filtered な元の圏へ制限し、同じ比較同値で存在を元へ移す。
規約：局所添字自体の厳密な小ささや元の比較の単射性を仮定しない。
使われ方：coherent な左 Kan 拡張の存在の組み立て。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
variable (κ : Cardinal.{u}) [Fact κ.IsRegular] {C : SSet.{u}} [Quasicategory C]
  {D : SSet.{u + 1}} [Quasicategory D]

/-- 元の Yoneda の全ての局所 Kan 図式は、小さい κ-filtered 余極限の存在だけで余極限を持つ。 -/
lemma indLeftKanDiagram_hasColimit (hD : HasSmallKappaFilteredColimits κ D)
    (F₀ : (SSet.uliftFunctor.{u + 1, u}).obj C ⟶ D) (v : (IndInfinity κ C) _⦋0⦌) :
    HasColimit (leftKanDiagram (indYoneda κ C) F₀ v) := by
  have := indVertexElements_isKappaFiltered κ v
  have hsmall := hD (smallRightUnstraightening (indVertexPresheaf κ v))
    ((SSet.uliftFunctor.{u + 1, u}).map
      (smallRightUnstraighteningProjection (indVertexPresheaf κ v)) ≫ F₀)
  have hrestrict : HasColimit (indElementsLeftKanComparison κ v ≫
      leftKanDiagram (indYoneda κ C) F₀ v) := by
    rw [indElementsLeftKanComparison_diagram]
    exact hsmall
  exact hasColimit_of_equivalentRestriction (indElementsLeftKanComparison κ v)
    (indElementsLeftKanComparison_isQCatEquivalence κ v) _ hrestrict

end SerrePositivity.InfinityCategories.F2.Ind
