module
public import SerrePositivity.KST.Comparison.GroupCompletion
public import Mathlib.Algebra.Group.Equiv.Opposite
public import Mathlib.AlgebraicTopology.SimplicialObject.Op

/-!
# 単体的モノイドの係数反転と反対モノイド

概要：係数方向の rev と各次数の反対モノイドを合わせた実単体的モノイドを作る。
方針：反対乗法を保つ実準同型を全ての単体射に適用する。
規約：KST Proposition 4.14、SW92 §1.2。nerve 方向だけの反転とは区別する。
使われ方：非可換な行側比較と対角 bar 全体の反転の接続。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.KST.ProExcision
open CategoryTheory Opposite

/-- 概要：係数の単体方向と乗法方向を両方反転した実モノイド図式。
方針：rev した係数写像に反対モノイド準同型を適用する。
規約：KST Proposition 4.14、SW92 §1.2。
使われ方：対角 bar の全反転との自然同型の入力。 -/
def monoidReverseOpposite (M : SimplicialObject MonCat.{u}) :
    SimplicialObject MonCat.{u} where
  obj k := MonCat.of (M.obj k)ᵐᵒᵖ
  map f := MonCat.ofHom (MonoidHom.op
    (M.map (SimplexCategory.rev.map f.unop).op).hom)
  map_id k := by
    apply MonCat.hom_ext
    apply MonoidHom.ext
    intro x
    apply MulOpposite.unop_injective
    change (M.map (SimplexCategory.rev.map (𝟙 k).unop).op).hom
      (MulOpposite.unop x) = MulOpposite.unop x
    simp
  map_comp f g := by
    apply MonCat.hom_ext
    apply MonoidHom.ext
    intro x
    apply MulOpposite.unop_injective
    change (M.map (SimplexCategory.rev.map (f ≫ g).unop).op).hom
      (MulOpposite.unop x) =
      (M.map (SimplexCategory.rev.map g.unop).op).hom
        ((M.map (SimplexCategory.rev.map f.unop).op).hom (MulOpposite.unop x))
    simp

/-- 概要：単体的モノイドの実射を係数反転と反対モノイドに沿って移す。
方針：各成分の反対準同型を実自然性で束ねる。
規約：SW92 §1.2。使われ方：反対 bar 同型の写像への自然性。 -/
def monoidReverseOppositeMap {M N : SimplicialObject MonCat.{u}} (f : M ⟶ N) :
    monoidReverseOpposite M ⟶ monoidReverseOpposite N where
  app k := MonCat.ofHom (MonoidHom.op (f.app k).hom)
  naturality {k l} φ := by
    apply MonCat.hom_ext
    apply MonoidHom.ext
    intro x
    apply MulOpposite.unop_injective
    exact congrArg (fun h : M.obj k ⟶ N.obj l ↦ h.hom (MulOpposite.unop x))
      (f.naturality (SimplexCategory.rev.map φ.unop).op)

end SerrePositivity.KST.ProExcision
