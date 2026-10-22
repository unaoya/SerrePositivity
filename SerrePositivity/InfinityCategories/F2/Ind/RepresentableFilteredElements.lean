module

public import SerrePositivity.InfinityCategories.F2.Ind.FilteredElementsCondition
public import SerrePositivity.InfinityCategories.F2.Ind.TerminalFiltered
public import SerrePositivity.InfinityCategories.F1.CanonicalYonedaUnstraighteningIdentity

/-!
概要：元の Yoneda 像の right unstraightening の元の圏は、任意の κ に対して κ-filtered。
方針：元の left unstraightening の標準恒等点の始対象性を反転し、終対象の余錐を使う。
規約：同じ元の表現可能前層を使い、別の表現可能モデルへ置き換えない。
使われ方：HTT 5.3.5.4 の最小閉包に入れる頂点条件の Yoneda 部分。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
variable (κ : Cardinal.{u}) {C : SSet.{u}} [Quasicategory C]

/-- 元の表現可能前層の元の圏は、元の恒等点を終対象として κ-filtered。 -/
lemma representablePresheaf_kappaFiltered_elements (x : C _⦋0⦌) :
    IsKappaFiltered κ (smallRightUnstraightening (representablePresheafInfinity x)) :=
  isKappaFiltered_of_isTerminalVertex κ
    (canonicalYonedaUnstraighteningIdentity_isInitialVertex x).op_isTerminalVertex

/-- 元の全 Yoneda の各頂点は、元の圏が κ-filtered であるという同じ頂点条件を満たす。 -/
lemma hasKappaFilteredElements_yoneda (x : C _⦋0⦌) :
    HasKappaFilteredElements κ ((yonedaInfinityMap C).app (Opposite.op ⦋0⦌) (ULift.up x)) := by
  rw [yonedaInfinityMap_vertex, hasKappaFilteredElements_functorVertex]
  exact representablePresheaf_kappaFiltered_elements κ x

end SerrePositivity.InfinityCategories.F2.Ind
