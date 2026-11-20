module


public import SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange

/-!
概要：対称モノイダル圏の内部 Hom の二つの交換同型は互いに逆。
方針：curry の同型を展開し、braiding の対称性を使う。
規約：単に braided でなく symmetric を仮定する。
使われ方：Goerss–Jardine I §7。二通りの loop 交換の向きの同定。
-/

@[expose] public section
universe v u
open CategoryTheory MonoidalCategory MonoidalClosed

namespace SerrePositivity.KST.Spectra.InternalHomExchange
end SerrePositivity.KST.Spectra.InternalHomExchange
namespace SerrePositivity.InfinityCategories.Project.PointedSpaces
open _root_.SerrePositivity.KST.Spectra.InternalHomExchange

noncomputable section
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
  [MonoidalClosed C]

/-- 逆順で源を交換する同型の順射は、元の交換同型の逆射。 -/
lemma hom_eq_inv (A K Y : C) : (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso A K Y).hom = (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso K A Y).inv := by
  simp only [_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso, Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv, _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.preIso]
  rw [SymmetricCategory.braiding_swap_eq_inv_braiding K A]
  simp only [Category.assoc]

end
end SerrePositivity.InfinityCategories.Project.PointedSpaces

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section
