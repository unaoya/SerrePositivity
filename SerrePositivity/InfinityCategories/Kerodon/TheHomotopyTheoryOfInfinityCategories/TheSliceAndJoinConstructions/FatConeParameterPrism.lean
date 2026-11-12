module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.FatConeCylinderIso
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.FixedFatConeUniversal

/-!
概要：固定頂点の fat join の錐の全族を、定値始域から元の図式への円柱の族へ移す。
方針：錐の関手空間の評価を、元の図式の円柱で前合成する。
規約：図式・頂点と任意の追加パラメータを厳密に保持する。
使われ方：全試験空間の極限判定と定値始域比較を結ぶ。

対応節は Kerodon 4.3（Tag 015M）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions

variable {K X T U : SSet.{u}} {f : K ⟶ X} {z : X _⦋0⦌}

/-- 固定頂点の fat 錐の全族を内部 Hom で評価する。 -/
def fixedFatConeFamilyEvaluation (f : K ⟶ X) (z : X _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fixedEndpointFatConeSpace f z ⟶ (ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoin Δ[0] K)).obj X :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι ((pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinEndpointInclusion (Δ[0] : SSet.{u}) K)).app X)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinEndpointDesc (SSet.yonedaEquiv.symm z) f))

/-- 頂点固定の錐の族を元の図式の円柱上で評価する。 -/
def fatConeParameterPrism (a : T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fixedEndpointFatConeSpace f z) :
    (K ⊗ (Δ[1] : SSet.{u})) ⊗ T ⟶ X :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.fatConeCylinderMap K ▷ T) ≫ uncurry (a ≫ fixedFatConeFamilyEvaluation f z)

/-- 元の錐の円柱の始点は同じ指定頂点に定値。 -/
lemma fatConeParameterPrism_zero (a : T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fixedEndpointFatConeSpace f z) :
    (SSet.ι₀ ▷ T) ≫ fatConeParameterPrism a = SSet.const z := by
  rw [fatConeParameterPrism, fixedFatConeFamilyEvaluation, ← Category.assoc, ← comp_whiskerRight, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.fatConeCylinderMap_zero,
    comp_whiskerRight, Category.assoc, ← uncurry_pre_app, Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fixedFatConeSpace_inl, SSet.comp_const, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.uncurry_const_functorVertex,
    SSet.yonedaEquiv_symm_zero, SSet.comp_const, SSet.comp_const]

/-- 元の錐の円柱の終点は同じ元の図式。 -/
lemma fatConeParameterPrism_one (a : T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fixedEndpointFatConeSpace f z) :
    (SSet.ι₁ ▷ T) ≫ fatConeParameterPrism a = fst K T ≫ f := by
  rw [fatConeParameterPrism, fixedFatConeFamilyEvaluation, ← Category.assoc, ← comp_whiskerRight, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.fatConeCylinderMap_one,
    ← uncurry_pre_app, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fixedFatConeSpace_inr,
    SSet.comp_const, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.uncurry_const_functorVertex]

/-- 円柱表示は任意の部分族への制限と厳密に可換。 -/
lemma fatConeParameterPrism_precomp (i : T ⟶ U) (a : U ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fixedEndpointFatConeSpace f z) :
    fatConeParameterPrism (i ≫ a) =
      ((K ⊗ (Δ[1] : SSet.{u})) ◁ i) ≫ fatConeParameterPrism a := by
  rw [fatConeParameterPrism, fatConeParameterPrism, Category.assoc, uncurry_natural_left,
    ← Category.assoc, ← whisker_exchange, Category.assoc]

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
