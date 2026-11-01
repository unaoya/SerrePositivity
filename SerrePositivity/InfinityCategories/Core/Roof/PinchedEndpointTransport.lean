module
public import SerrePositivity.InfinityCategories.Core.MappingSpaceMap

/-! # pinched 写像空間の端点等式による輸送

概要：等しい端点を持つ写像空間を同型で同定する。
方針：等式の帰納法で同型を作り、元の単体を変えないことを証明する。
規約：端点の同型による輸送とは区別する。使われ方：β3 の dg 関手の線形表示。
-/
@[expose] public section
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory SSet
open scoped Simplicial

/-- 端点の等式による pinched 写像空間の同型。 -/
def pinchedEndpointIso {X : SSet.{u}} {x y x' y' : X _⦋0⦌}
    (hx : x = x') (hy : y = y') : pinchedHom x y ≅ pinchedHom x' y' := by
  subst x'
  subst y'
  exact Iso.refl _

/-- 端点の等式による輸送は元の単体を変えない。 -/
lemma pinchedEndpointIso_hom_val {X : SSet.{u}} {x y x' y' : X _⦋0⦌}
    (hx : x = x') (hy : y = y') {n : ℕ} (s : (pinchedHom x y) _⦋n⦌) :
    ((pinchedEndpointIso hx hy).hom.app (Opposite.op ⦋n⦌) s).val = s.val := by
  subst x'
  subst y'
  rfl

end SerrePositivity.InfinityCategories
