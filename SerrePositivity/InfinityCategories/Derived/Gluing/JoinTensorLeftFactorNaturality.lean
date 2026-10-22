module
public import SerrePositivity.InfinityCategories.Core.JoinTensorInterval

/-! join の左 tensor 比較は、join の第一因子の射についても全単体で自然。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial

lemma dgGluingJoinTensorLeft_factor_naturality (K C : SSet.{u}) {B B' : SSet.{u}}
    (f : B ⟶ B') :
    (K ◁ joinMap f (𝟙 C)) ≫ joinTensorLeft K B' C =
      joinTensorLeft K B C ≫ joinMap (K ◁ f) (𝟙 C) := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨k, ⟨ℓ, b, c⟩⟩
  change Join.tensorLeftSimplex K B' C n k
      ⟨ℓ, Join.augHom f ℓ.val b, Join.augHom (𝟙 C) (n + 1 - ℓ.val) c⟩ =
    (⟨ℓ, Join.augHom (K ◁ f) ℓ.val ((Join.augTensorEquiv K B ℓ.val).symm
        (Join.augMap K (Join.prefixIncl (n + 1) ℓ.val (Nat.le_of_lt_succ ℓ.isLt)) k, b)),
      Join.augHom (𝟙 C) (n + 1 - ℓ.val) c⟩ : Join.Simplex (K ⊗ B') C n)
  rw [Join.augTensorEquiv_symm_augHomRight]
  rfl

end SerrePositivity.InfinityCategories
