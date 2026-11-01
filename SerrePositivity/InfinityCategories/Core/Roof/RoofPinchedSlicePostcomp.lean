module
public import SerrePositivity.InfinityCategories.Core.PinchedSlice
public import SerrePositivity.InfinityCategories.Core.Roof.PinchedEndpointTransport
public import SerrePositivity.InfinityCategories.Core.Roof.SliceOverEqualityTransport

/-! # 実 pinched Hom の slice 表示と標的の後合成

概要：pinched Hom の実 slice 表示は、端点の等式輸送を含む後合成と厳密に可換。
方針：両側の台の join 射を比較し、固定図式・端点の輸送を外して Yoneda の自然性を使う。
規約：任意の単体集合と任意の次数。使われ方：商比較の全 fiber での同定。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory SSet
open scoped Simplicial

/-- pinched Hom の slice への包含は、端点輸送を含む後合成と全次元で可換。 -/
lemma roofPinchedSlice_postcomp {X Y : SSet.{u}} (f : X ⟶ Y) (x y : X _⦋0⦌)
    {x' y' : Y _⦋0⦌} (hx : f.app (Opposite.op ⦋0⦌) x = x')
    (hy : f.app (Opposite.op ⦋0⦌) y = y')
    (hp : SSet.yonedaEquiv.symm y ≫ f = SSet.yonedaEquiv.symm y') :
    (pinchedHomSliceFiberIso x y).hom ≫
      vertexFiberι (sliceOverProjection (SSet.yonedaEquiv.symm y)) x ≫
      sliceOverPostcomp (SSet.yonedaEquiv.symm y) f ≫
      (eqToIso (congrArg sliceOver hp)).hom =
    pinchedHomMap f x y ≫ (pinchedEndpointIso hx hy).hom ≫
      (pinchedHomSliceFiberIso x' y').hom ≫
      vertexFiberι (sliceOverProjection (SSet.yonedaEquiv.symm y')) x' := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro s
  apply Subtype.ext
  change ((eqToIso (congrArg sliceOver hp)).hom.app _
    ((sliceOverPostcomp (SSet.yonedaEquiv.symm y) f).app _
      (pinchedSimplexToFiber s).val)).val =
    (joinStdSimplexIso n 0).hom ≫ SSet.yonedaEquiv.symm
      (((pinchedEndpointIso hx hy).hom.app _ (pinchedSimplexMap f s)).val)
  rw [roofSliceTransport_val hp, pinchedEndpointIso_hom_val]
  change ((joinStdSimplexIso n 0).hom ≫ SSet.yonedaEquiv.symm s.val) ≫ f =
    (joinStdSimplexIso n 0).hom ≫ SSet.yonedaEquiv.symm
      (f.app (Opposite.op ⦋n + 1⦌) s.val)
  rw [Category.assoc, SSet.yonedaEquiv_symm_comp]

end SerrePositivity.InfinityCategories
