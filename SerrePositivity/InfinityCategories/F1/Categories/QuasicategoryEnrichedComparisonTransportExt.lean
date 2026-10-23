module

public import SerrePositivity.InfinityCategories.F1.Categories.QuasicategoryEnrichedDiagramComparisonExt
public import SerrePositivity.InfinityCategories.F1.Categories.QuasicategoryEnrichedDiagramArrow

/-!
概要：元の豊穣関手の表示の等式を保ち、指定比較の成分一致を比較全体の一致へ移す。
方針：両端の関手・図式の等式を消去し、同じ成分の外延性を使う。
規約：指定された比較を選び直さない。
使われ方：全局所比較の族と元の大域結合比較の族を同定する。
-/

@[expose] public section
noncomputable section
universe u v
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories

/-- 両端が等しい豊穣関手の指定比較は、同じ全成分を持てば型を含めて等しい。 -/
lemma QuasicategoryEnrichedComparison.heq_of_components
    {C : Type v} [Category.{u} C] [SimplicialCategory C]
    {F G F' G' : EnrichedFunctor SSet.{u} C QuasicategoryObject.{u}}
    (hf : F = F') (hg : G = G')
    (e : QuasicategoryEnrichedComparison F G) (e' : QuasicategoryEnrichedComparison F' G')
    (h : ∀ X, HEq (e.val X) (e'.val X)) : HEq e e' := by
  subst F' G'
  apply heq_of_eq
  apply Subtype.ext
  funext X
  exact eq_of_heq (h X)

/-- 両端の図式と全比較成分の同じ値は、元の区間図式全体の等式を与える。 -/
lemma QuasicategoryEnrichedDiagramComparison.arrowDiagram_eq_of_components
    {C : Type v} [Category.{u} C] [SimplicialCategory C]
    {J : Type u} [Category.{u} J] {D E D' E' : QuasicategoryEnrichedDiagram C J}
    (hd : D = D') (he : E = E')
    (e : QuasicategoryEnrichedDiagramComparison D E)
    (e' : QuasicategoryEnrichedDiagramComparison D' E')
    (h : ∀ j X, HEq ((e.app j).val X) ((e'.app j).val X)) :
    e.arrowDiagram = e'.arrowDiagram := by
  subst D' E'
  have hh : e = e' := QuasicategoryEnrichedDiagramComparison.extPointwise
    (fun j X ↦ eq_of_heq (h j X))
  rw [hh]

end SerrePositivity.InfinityCategories
