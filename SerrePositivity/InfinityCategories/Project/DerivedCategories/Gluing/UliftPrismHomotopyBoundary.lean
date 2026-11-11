module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.UliftPrismHomotopy
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IntervalBoundary

/-! 同じ全二次元族の宇宙移送は、元 prism の両端固定条件を厳密に保存する。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped _root_.Simplicial
variable {K X : SSet.{u}} {F G : (Δ[1] : SSet.{u}) ⊗ K ⟶ X}
  (H : SSet.Homotopy F G)
  (hH : (((boundary 1).ι ▷ K) ▷ (Δ[1] : SSet.{u})) ≫ H.h =
    fst ((boundary 1 : SSet.{u}) ⊗ K) Δ[1] ≫ ((boundary 1).ι ▷ K) ≫ G)

include hH in
lemma dgGluingUliftPrismHomotopy_boundary :
    (((boundary 1).ι ▷ (SSet.uliftFunctor.{v, u}).obj K) ▷
        (Δ[1] : SSet.{max u v})) ≫ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUliftPrismHomotopy.{u, v} H).h =
      fst ((boundary 1 : SSet.{max u v}) ⊗ (SSet.uliftFunctor.{v, u}).obj K) Δ[1] ≫
        ((boundary 1).ι ▷ (SSet.uliftFunctor.{v, u}).obj K) ≫
          _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUliftSimplexFamily.{u, v} 1 G := by
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  rintro ⟨⟨z, k⟩, t⟩
  apply ULift.ext
  let z' : (boundary 1 : SSet.{u}).obj d := ⟨ULift.up z.val.down, z.property⟩
  let w : (((boundary 1 : SSet.{u}) ⊗ K) ⊗ (Δ[1] : SSet.{u})).obj d :=
    ((z', k.down), ULift.up t.down)
  exact ConcreteCategory.congr_hom (C := Type u)
    (X := (((boundary 1 : SSet.{u}) ⊗ K) ⊗ (Δ[1] : SSet.{u})).obj d)
    (Y := X.obj d) (NatTrans.congr_app hH d) w

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
