module

public import Mathlib.Algebra.Homology.Homotopy

/-!
概要：零ホモトピー直交性を始域の同型で移送する。
方針：逆同型で射を移し、得たホモトピーを同型で前合成する。
規約：実際の複体の同型を使う。
使われ方：Stacks Lemma 19.12.3、TT §3・§8、Toën §3.2 の小さい試験商の同定。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits
namespace SerrePositivity.KST.DerivedGeometry
variable {C : Type*} [Category* C] [Preadditive C] {ι : Type*} {c : ComplexShape ι}

/--
概要：同型な始域は同じ零ホモトピー直交性を持つ。
方針：同型による前合成と逆性を使う。
規約：複体の非輪状性をこの補題には仮定しない。
使われ方：Stacks 19.12.3、TT §3 の後続商の比較。
-/
lemma homotopy_orthogonal_of_iso {K L I : HomologicalComplex C c} (e : K ≅ L)
    (h : ∀ f : L ⟶ I, Nonempty (Homotopy f 0)) (f : K ⟶ I) : Nonempty (Homotopy f 0) := by
  have ht := (h (e.inv ≫ f)).some.compLeft e.hom
  exact ⟨by simpa only [← Category.assoc, Iso.hom_inv_id, Category.id_comp, comp_zero] using ht⟩

end SerrePositivity.KST.DerivedGeometry
