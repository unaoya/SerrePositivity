module

public import SerrePositivity.InfinityCategories.F2.Presentable.SliceOverCoconeBackward

/-!
概要：対象上の余錐圏を、底の余錐圏内の増大余錐上の slice と全同型で比較する。
方針：両比較の任意パラメーターでの uncurry を計算して逆則を示す。
規約：単体集合の厳密な同型であり、頂点・辺の照合に弱めない。
使われ方：対象上の余極限性を底の余錐の始対象性から検出する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable
variable {K X : SSet.{u}} (x : (Δ[0] : SSet.{u}) ⟶ X) (a : K ⟶ sliceOver x)

/-- 概要：順比較の二回の uncurry は任意の全パラメーターに対して逆結合で計算できる。
方針：両 uncurry の自然性と逆結合同型の自然性を使う。
規約：パラメーターの quasicategory 性を要求しない。
使われ方：逆比較との全射の逆則。 -/
lemma sliceOverCoconeForward_uncurry_comp {A : SSet.{u}} (f : A ⟶ sliceUnder a) :
    sliceUnderUncurry (sliceOverUncurry (f ≫ sliceOverCoconeForward x a)) =
      (stableJoinAssociator K A Δ[0]).inv ≫ sliceOverUncurry (sliceUnderUncurry f) := by
  rw [sliceOverUncurry_precomp, sliceUnderUncurry_precomp, sliceOverCoconeForward_uncurry]
  dsimp only [sliceOverCoconeForwardDiagram]
  rw [← Category.assoc, joinAssociator_inv_naturality, Category.assoc,
    ← sliceOverUncurry_precomp, ← sliceUnderUncurry_precomp, Category.comp_id]

/-- 概要：逆比較の二回の uncurry は任意の全パラメーターに対して順結合で計算できる。
方針：両 uncurry の自然性と結合同型の自然性を使う。
規約：元の増大余錐を固定する。
使われ方：順比較との全射の逆則。 -/
lemma sliceOverCoconeBackward_uncurry_comp {A : SSet.{u}}
    (g : A ⟶ sliceOver (SSet.yonedaEquiv.symm (sliceOverAugmentationCocone x a))) :
    sliceOverUncurry (sliceUnderUncurry (g ≫ sliceOverCoconeBackward x a)) =
      (stableJoinAssociator K A Δ[0]).hom ≫ sliceUnderUncurry (sliceOverUncurry g) := by
  rw [sliceUnderUncurry_precomp, sliceOverUncurry_precomp, sliceOverCoconeBackward_uncurry]
  dsimp only [sliceOverCoconeBackwardDiagram]
  rw [← Category.assoc, stableJoinAssociator_naturality, Category.assoc,
    ← sliceUnderUncurry_precomp, ← sliceOverUncurry_precomp, Category.comp_id]

/-- 概要：対象上の余錐圏と底の余錐圏内の元の増大余錐上の slice は厳密に同型。
方針：二重 uncurry の単射性で両合成を判定し、結合同型を打ち消す。
規約：全ての単体と固定対象への整合を保持する。
使われ方：対象上の図式の余極限性の底での検出。 -/
def sliceOverCoconeIso : sliceUnder a ≅
    sliceOver (SSet.yonedaEquiv.symm (sliceOverAugmentationCocone x a)) where
  hom := sliceOverCoconeForward x a
  inv := sliceOverCoconeBackward x a
  hom_inv_id := by
    apply sliceUnderUncurry_injective a
    apply sliceOverUncurry_injective x
    rw [sliceOverCoconeBackward_uncurry_comp, sliceOverCoconeForward_uncurry]
    dsimp only [sliceOverCoconeForwardDiagram]
    rw [Iso.hom_inv_id_assoc]
  inv_hom_id := by
    apply sliceOverUncurry_injective (SSet.yonedaEquiv.symm (sliceOverAugmentationCocone x a))
    apply sliceUnderUncurry_injective (a ≫ sliceOverProjection x)
    rw [sliceOverCoconeForward_uncurry_comp, sliceOverCoconeBackward_uncurry]
    dsimp only [sliceOverCoconeBackwardDiagram]
    rw [Iso.inv_hom_id_assoc]

end SerrePositivity.InfinityCategories.F2.Presentable
