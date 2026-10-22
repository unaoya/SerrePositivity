module

public import SerrePositivity.InfinityCategories.F2.Ind.PresheafDensity
public import SerrePositivity.InfinityCategories.F2.Ind.FilteredClosure

/-!
概要：元の right unstraightening の元の圏が κ-filtered なら、同じ前層は Indκ の最小閉包に属する。
方針：元の F を頂点とする同じ密度余極限を、最小閉包の κ-filtered 余極限閉性へ入力する。
規約：κ-filtered 性は F2N-1 の元の定義を明示的な仮定として使う。逆向きは別工程。
使われ方：HTT 5.3.5.4 の右 fibration 条件から最小閉包への方向。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
variable {C : SSet.{u}} [Quasicategory C]
  (κ : Cardinal.{u}) (F : (SSet.uliftFunctor.{u + 1, u}).obj C.op ⟶ SpaceInfinity.{u})

/-- 同じ元の圏が κ-filtered なら、元の F は表現可能前層の最小 κ-filtered 閉包に属する。 -/
lemma isIndVertex_of_kappaFiltered_elements
    (hF : IsKappaFiltered κ (smallRightUnstraightening F)) :
    IsIndVertex κ C (functorVertex F) := by
  have := hF
  have h := isIndVertex_kappaColimitClosed κ C (smallRightUnstraightening F)
    (presheafElementsYonedaDiagram F) (presheafDensityCocone F)
    (presheafDensityCocone_isColimit F) (fun e =>
      isIndVertex_yoneda κ ((smallRightUnstraighteningProjection F).app (Opposite.op ⦋0⦌) e))
  simpa only [presheafDensityCocone_vertex] using h

end SerrePositivity.InfinityCategories.F2.Ind
