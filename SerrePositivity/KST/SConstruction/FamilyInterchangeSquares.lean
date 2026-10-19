module
public import SerrePositivity.KST.SConstruction.FamilyChainPairing

/-! # 元の二つの実円柱の区間交換正方形
概要：二つの独立な実区間を同じ二次元円柱へ組み込み、四辺を厳密に回収する。
方針：二つの時刻を独立に射影し、共通パラメータ上の二つの円柱を積で合成する。
規約：Kan 性や区間の取り替えを使わず、元の各実円柱を全時刻で保つ。
使われ方：K の合成補正と適合円柱の区間順序の交換。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
variable {U E F G : SSet.{u}}
  (h : U ⊗ (Δ[1] : SSet.{u}) ⟶ E) (k : U ⊗ (Δ[1] : SSet.{u}) ⟶ F) (m : E ⊗ F ⟶ G)

/-- 元の二つの円柱を独立な二つの時刻で組にした実正方形。 -/
def familyInterchangeSquare : (U ⊗ (Δ[1] : SSet.{u})) ⊗ (Δ[1] : SSet.{u}) ⟶ G :=
  lift (fst (U ⊗ Δ[1]) Δ[1] ≫ h)
    (lift (fst (U ⊗ Δ[1]) Δ[1] ≫ fst U Δ[1]) (snd (U ⊗ Δ[1]) Δ[1]) ≫ k) ≫ m

/-- 第二時刻の零面は、第一の元の円柱と第二の元の始点との合成。 -/
lemma familyInterchangeSquare_second_zero :
    SSet.ι₀ ≫ familyInterchangeSquare h k m = lift h (fst U Δ[1] ≫ SSet.ι₀ ≫ k) ≫ m := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro x
  rfl

/-- 第二時刻の一面は、第一の元の円柱と第二の元の終点との合成。 -/
lemma familyInterchangeSquare_second_one :
    SSet.ι₁ ≫ familyInterchangeSquare h k m = lift h (fst U Δ[1] ≫ SSet.ι₁ ≫ k) ≫ m := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro x
  rfl

/-- 第一時刻の零面は、第一の元の始点と第二の元の円柱との合成。 -/
lemma familyInterchangeSquare_first_zero :
    (SSet.ι₀ (X := U) ▷ (Δ[1] : SSet.{u})) ≫ familyInterchangeSquare h k m =
      lift (fst U Δ[1] ≫ SSet.ι₀ ≫ h) k ≫ m := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro x
  rfl

/-- 第一時刻の一面は、第一の元の終点と第二の元の円柱との合成。 -/
lemma familyInterchangeSquare_first_one :
    (SSet.ι₁ (X := U) ▷ (Δ[1] : SSet.{u})) ≫ familyInterchangeSquare h k m =
      lift (fst U Δ[1] ≫ SSet.ι₁ ≫ h) k ≫ m := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro x
  rfl

/-- 元の共通パラメータの任意の制限は、二時刻を保って正方形の構成と可換。 -/
lemma familyInterchangeSquare_restrict {T : SSet.{u}} (j : T ⟶ U) :
    ((j ▷ (Δ[1] : SSet.{u})) ▷ (Δ[1] : SSet.{u})) ≫ familyInterchangeSquare h k m =
      familyInterchangeSquare ((j ▷ (Δ[1] : SSet.{u})) ≫ h)
        ((j ▷ (Δ[1] : SSet.{u})) ≫ k) m := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro x
  rfl

end SerrePositivity.KST.SConstruction
