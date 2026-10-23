module

public import SerrePositivity.InfinityCategories.F1.Joins.ConeCylinderMap
public import SerrePositivity.InfinityCategories.HomotopyLimits.FixedEndpointConeSpace

/-!
概要：固定頂点の native な錐の全族を、定値始域から元の図式への円柱の族へ移す。
方針：錐の関手空間の評価を、元の図式の円柱で前合成する。
規約：図式・頂点と任意の追加パラメータを厳密に保持する。
使われ方：全試験空間の極限判定と定値始域比較を結ぶ。
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
variable {K X T U : SSet.{u}} {f : K ⟶ X} {z : X _⦋0⦌}

/-- 頂点固定の錐の族を元の図式の円柱上で評価する。 -/
def coneParameterPrism (a : T ⟶ fixedApexConeFamily f z) :
    (K ⊗ (Δ[1] : SSet.{u})) ⊗ T ⟶ X :=
  (coneCylinderMap K ▷ T) ≫ uncurry (a ≫ fixedApexConeFamilyEvaluation f z)

/-- 元の錐の円柱の始点は同じ指定頂点に定値。 -/
lemma coneParameterPrism_zero (a : T ⟶ fixedApexConeFamily f z) :
    (SSet.ι₀ ▷ T) ≫ coneParameterPrism a = SSet.const z := by
  rw [coneParameterPrism, ← Category.assoc, ← comp_whiskerRight, coneCylinderMap_zero,
    comp_whiskerRight, Category.assoc, ← uncurry_pre_app, Category.assoc,
    fixedApexConeFamilyEvaluation_inl, SSet.comp_const, uncurry_const_functorVertex,
    SSet.yonedaEquiv_symm_zero, SSet.comp_const, SSet.comp_const]

/-- 元の錐の円柱の終点は同じ元の図式。 -/
lemma coneParameterPrism_one (a : T ⟶ fixedApexConeFamily f z) :
    (SSet.ι₁ ▷ T) ≫ coneParameterPrism a = fst K T ≫ f := by
  rw [coneParameterPrism, ← Category.assoc, ← comp_whiskerRight, coneCylinderMap_one,
    ← uncurry_pre_app, Category.assoc, fixedApexConeFamilyEvaluation_inr,
    SSet.comp_const, uncurry_const_functorVertex]

/-- 円柱表示は任意の部分族への制限と厳密に可換。 -/
lemma coneParameterPrism_precomp (i : T ⟶ U) (a : U ⟶ fixedApexConeFamily f z) :
    coneParameterPrism (i ≫ a) =
      ((K ⊗ (Δ[1] : SSet.{u})) ◁ i) ≫ coneParameterPrism a := by
  rw [coneParameterPrism, coneParameterPrism, Category.assoc, uncurry_natural_left,
    ← Category.assoc, ← whisker_exchange, Category.assoc]

end SerrePositivity.InfinityCategories
