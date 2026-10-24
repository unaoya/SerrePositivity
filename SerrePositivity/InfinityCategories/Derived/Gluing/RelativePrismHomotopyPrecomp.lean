module
public import SerrePositivity.InfinityCategories.Derived.Gluing.RelativePrismHomotopy
public import SerrePositivity.InfinityCategories.F1B.Homotopy.HomotopyWhiskering

/-! 元パラメーターへの制限は、全 prism 比較の両端固定条件を厳密に保存する。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
variable {K L X : SSet.{u}} {F G : (Δ[1] : SSet.{u}) ⊗ L ⟶ X}
  (H : SSet.Homotopy F G) (a : K ⟶ L)
  (hH : (((boundary 1).ι ▷ L) ▷ (Δ[1] : SSet.{u})) ≫ H.h =
    fst ((boundary 1 : SSet.{u}) ⊗ L) Δ[1] ≫ ((boundary 1).ι ▷ L) ≫ G)

include hH in
lemma dgGluingRelativePrismHomotopy_precomp_boundary :
    (((boundary 1).ι ▷ K) ▷ (Δ[1] : SSet.{u})) ≫
        (functorHomotopyPrecomp H ((Δ[1] : SSet.{u}) ◁ a)).h =
      fst ((boundary 1 : SSet.{u}) ⊗ K) Δ[1] ≫ ((boundary 1).ι ▷ K) ≫
        ((Δ[1] : SSet.{u}) ◁ a) ≫ G := by
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  rintro ⟨⟨z, k⟩, t⟩
  let w : (((boundary 1 : SSet.{u}) ⊗ L) ⊗ (Δ[1] : SSet.{u})).obj d :=
    ((z, a.app d k), t)
  exact ConcreteCategory.congr_hom (C := Type u)
    (X := (((boundary 1 : SSet.{u}) ⊗ L) ⊗ (Δ[1] : SSet.{u})).obj d)
    (Y := X.obj d) (NatTrans.congr_app hH d) w

end SerrePositivity.InfinityCategories
