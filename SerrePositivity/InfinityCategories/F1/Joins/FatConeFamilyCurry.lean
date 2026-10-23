module

public import SerrePositivity.InfinityCategories.F1.Joins.FatConeParameterPrism

/-!
概要：両端固定の fat 錐の全族を、固定頂点の関手空間へ curry する。
方針：内部 Hom の curry の後、両端の直和上の固定条件を fiber に添える。
規約：任意の右パラメータと元の全図式を厳密に保持する。
使われ方：定値始域の変換から錐への逆比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories
open HomotopyLimits
variable {K X T : SSet.{u}} {f : K ⟶ X} {z : X _⦋0⦌}

/-- 同じ指定頂点と図式を持つ fat 錐の全族を、固定頂点の空間へ戻す。 -/
def fixedFatConeFamilyCurry (G : fatJoin Δ[0] K ⊗ T ⟶ X)
    (h₀ : (fatJoinInl Δ[0] K ▷ T) ≫ G = SSet.const z)
    (h₁ : (fatJoinInr Δ[0] K ▷ T) ≫ G = fst K T ≫ f) :
    T ⟶ fixedEndpointFatConeSpace f z :=
  vertexFiberLift _ _ (curry G) (by
    apply uncurry_injective
    rw [uncurry_pre_app, uncurry_curry, uncurry_const_functorVertex]
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    rintro ⟨s, t⟩
    cases s with
    | inl d =>
      change (((fatJoinInl Δ[0] K ▷ T) ≫ G).app n (d, t)) =
        (fst (Δ[0] : SSet.{u}) T ≫ SSet.yonedaEquiv.symm z).app n (d, t)
      rw [h₀, SSet.yonedaEquiv_symm_zero, SSet.comp_const]
    | inr k =>
      change (((fatJoinInr Δ[0] K ▷ T) ≫ G).app n (k, t)) =
        (fst K T ≫ f).app n (k, t)
      rw [h₁])

/-- 同じ全族を curry した後に評価すると、元の全図式を厳密に回収する。 -/
lemma fixedFatConeFamilyCurry_uncurry (G : fatJoin Δ[0] K ⊗ T ⟶ X)
    (h₀ : (fatJoinInl Δ[0] K ▷ T) ≫ G = SSet.const z)
    (h₁ : (fatJoinInr Δ[0] K ▷ T) ≫ G = fst K T ≫ f) :
    uncurry (fixedFatConeFamilyCurry G h₀ h₁ ≫ fixedFatConeFamilyEvaluation f z) = G := by
  rw [fixedFatConeFamilyCurry, fixedFatConeFamilyEvaluation, vertexFiberLift_ι, uncurry_curry]

/-- 同じ全族を curry した後の元の円柱は、元の全図式への同じ制限。 -/
lemma fixedFatConeFamilyCurry_prism (G : fatJoin Δ[0] K ⊗ T ⟶ X)
    (h₀ : (fatJoinInl Δ[0] K ▷ T) ≫ G = SSet.const z)
    (h₁ : (fatJoinInr Δ[0] K ▷ T) ≫ G = fst K T ≫ f) :
    fatConeParameterPrism (fixedFatConeFamilyCurry G h₀ h₁) = (fatConeCylinderMap K ▷ T) ≫ G := by
  rw [fatConeParameterPrism, fixedFatConeFamilyCurry_uncurry]

end SerrePositivity.InfinityCategories
