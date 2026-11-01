module
public import SerrePositivity.InfinityCategories.Core.Roof.PinchedEndpointTransport

/-! 可換な実二脚の写像空間作用を、同じ端点等式による輸送を含めて照合する。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory SSet
open scoped Simplicial
variable {T L A : SSet.{u}} (f : T ⟶ L) (p : L ⟶ A) (a : T ⟶ A) (h : f ≫ p = a)

include h in
lemma dgGluingPinchedComposite_vertex (x : T _⦋0⦌) :
    p.app (Opposite.op ⦋0⦌) (f.app (Opposite.op ⦋0⦌) x) = a.app (Opposite.op ⦋0⦌) x :=
  ConcreteCategory.congr_hom (NatTrans.congr_app h (Opposite.op ⦋0⦌)) x

def dgGluingPinchedCompositeIso (x y : T _⦋0⦌) :
    pinchedHom (p.app (Opposite.op ⦋0⦌) (f.app (Opposite.op ⦋0⦌) x))
        (p.app (Opposite.op ⦋0⦌) (f.app (Opposite.op ⦋0⦌) y)) ≅
      pinchedHom (a.app (Opposite.op ⦋0⦌) x) (a.app (Opposite.op ⦋0⦌) y) :=
  pinchedEndpointIso (dgGluingPinchedComposite_vertex f p a h x)
    (dgGluingPinchedComposite_vertex f p a h y)

lemma dgGluingPinchedComposite_naturality (x y : T _⦋0⦌) :
    pinchedHomMap f x y ≫
        pinchedHomMap p (f.app (Opposite.op ⦋0⦌) x) (f.app (Opposite.op ⦋0⦌) y) ≫
        (dgGluingPinchedCompositeIso f p a h x y).hom = pinchedHomMap a x y := by
  subst a
  rw [← Category.assoc, ← pinchedHomMap_comp]
  change pinchedHomMap (f ≫ p) x y ≫ 𝟙 _ = _
  rw [Category.comp_id]

end SerrePositivity.InfinityCategories
