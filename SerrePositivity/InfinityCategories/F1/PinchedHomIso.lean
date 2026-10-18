module

public import SerrePositivity.InfinityCategories.F1.CoherentHomEnrichedNaturality

/-!
概要：単体集合の同型で右 pinched 写像空間を厳密に移送する。
方針：同型とその逆が単体に作用する写像を用い、端点の往復の等号で逆の端点を揃える。
規約：quasicategory 性や Kan 性は不要。
使われ方：Kerodon §4.6.7、coherent nerve の反対の同型による左 Hom の解像模型の同定。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：単体集合の同型は対応する二頂点の右 pinched 写像空間の同型を誘導する。
方針：逆写像の端点を同型の往復則で正規化し、元の単体で逆則を確認する。
規約：順方向は元の同型の順方向の pinchedHomMap。
使われ方：Kerodon §4.6.7、反転した coherent nerve の右 Hom を反対圏の Hom へ厳密に移す。 -/
def pinchedHomIsoOfIso {X Y : SSet.{u}} (e : X ≅ Y) (x y : X _⦋0⦌) :
    pinchedHom x y ≅
      pinchedHom (e.hom.app (Opposite.op ⦋0⦌) x) (e.hom.app (Opposite.op ⦋0⦌) y) := by
  have hx : e.inv.app (Opposite.op ⦋0⦌) (e.hom.app (Opposite.op ⦋0⦌) x) = x :=
    ConcreteCategory.congr_hom (NatTrans.congr_app e.hom_inv_id _) x
  have hy : e.inv.app (Opposite.op ⦋0⦌) (e.hom.app (Opposite.op ⦋0⦌) y) = y :=
    ConcreteCategory.congr_hom (NatTrans.congr_app e.hom_inv_id _) y
  refine
    { hom := pinchedHomMap e.hom x y
      inv := pinchedHomMap e.inv _ _ ≫ eqToHom (congrArg₂ (fun a b ↦ pinchedHom a b) hx hy)
      hom_inv_id := ?_
      inv_hom_id := ?_ }
  · apply SSet.hom_ext
    rintro ⟨⟨n⟩⟩
    apply ConcreteCategory.hom_ext
    intro s
    apply PinchedHom.Simplex.ext
    change ((eqToHom (congrArg₂ (fun a b ↦ pinchedHom a b) hx hy)).app (Opposite.op ⦋n⦌)
      ((pinchedHomMap e.inv _ _).app _ ((pinchedHomMap e.hom x y).app _ s))).val = s.val
    rw [pinchedHom_eqToHom_app_val hx hy]
    exact ConcreteCategory.congr_hom (NatTrans.congr_app e.hom_inv_id _) s.val
  · apply SSet.hom_ext
    rintro ⟨⟨n⟩⟩
    apply ConcreteCategory.hom_ext
    intro s
    apply PinchedHom.Simplex.ext
    change e.hom.app (Opposite.op ⦋n + 1⦌)
      (((eqToHom (congrArg₂ (fun a b ↦ pinchedHom a b) hx hy)).app (Opposite.op ⦋n⦌)
        ((pinchedHomMap e.inv _ _).app _ s)).val) = s.val
    rw [pinchedHom_eqToHom_app_val hx hy]
    exact ConcreteCategory.congr_hom (NatTrans.congr_app e.inv_hom_id _) s.val

end SerrePositivity.InfinityCategories
