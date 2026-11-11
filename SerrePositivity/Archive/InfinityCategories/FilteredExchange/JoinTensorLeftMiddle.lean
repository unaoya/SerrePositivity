module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.JoinTensorInterval

/-!
概要：係数付き左錐への比較は、元の左の join 因子の全写像に自然。
方針：同じ切断の二つの左係数を補った直積の自然性で比較する。
規約：全単体・全係数を保持。使われ方：標準単体錐の面・退化の制限。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
namespace SerrePositivity.InfinityCategories.F2

/-- 元の join の左因子の全写像は、係数を追加する同じ比較と厳密に可換。 -/
lemma joinTensorLeft_middle_naturality {A B : SSet.{u}} (f : A ⟶ B) (P C : SSet.{u}) :
    (P ◁ joinMap f (𝟙 C)) ≫ joinTensorLeft P B C =
      joinTensorLeft P A C ≫ joinMap (P ◁ f) (𝟙 C) := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨p, ℓ, a, c⟩
  let q := Join.augMap P (Join.prefixIncl (n + 1) ℓ.val (Nat.le_of_lt_succ ℓ.isLt)) p
  change (⟨ℓ, (Join.augTensorEquiv P B ℓ.val).symm (q, Join.augHom f ℓ.val a),
      Join.augHom (𝟙 C) (n + 1 - ℓ.val) c⟩ : Join.Simplex (P ⊗ B) C n) =
    ⟨ℓ, Join.augHom (P ◁ f) ℓ.val ((Join.augTensorEquiv P A ℓ.val).symm (q, a)),
      Join.augHom (𝟙 C) (n + 1 - ℓ.val) c⟩
  rw [Join.augTensorEquiv_symm_augHomRight]

end SerrePositivity.InfinityCategories.F2
