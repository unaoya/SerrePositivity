module

public import SerrePositivity.EInfinity.SimplicialLocalization.KanHammockHomPinched

/-!
# 同じ Kan hammock Hom 比較の元の coherent 単体の値

概要：元の端点輸送を通した pinched 比較は元の coherent Hom 単体をそのまま保つ。
方針：元の全単体の値に関する端点輸送の式を使う。
規約：元の Hom・元の局所化頂点・同じ単体を保持する。
使われ方：native roof prism の実一端。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.SimplicialLocalization
open CategoryTheory SSet Hammock
open SerrePositivity.InfinityCategories SerrePositivity.KST.Comparison
open scoped Simplicial
variable (C : RelativeCategory.{u}) (X Y : C.category)

lemma kanHammockHomPinchedMap_app_val {n : ℕ}
    (s : (exInfinity.obj (colimitGraph C.weakEquivalences X Y)) _⦋n⦌) :
    ((kanHammockHomPinchedMap C X Y).app (Opposite.op ⦋n⦌) s).val =
      coherentHomComparisonSimplex (show (SimplicialCategory.sHom
        ((kanHammockSourceFunctor C).obj X) ((kanHammockSourceFunctor C).obj Y)) _⦋n⦌ from s) := by
  change ((pinchedEndpointIso (hammockLocalizationNerveMap_vertex C X).symm
    (hammockLocalizationNerveMap_vertex C Y).symm).hom.app (Opposite.op ⦋n⦌)
      (coherentHomComparisonPinchedSimplex s)).val = _
  rw [pinchedEndpointIso_hom_val]
  rfl

end SerrePositivity.EInfinity.SimplicialLocalization
