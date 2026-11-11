module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.CoconeUnitFamilyEndpoints
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.ConstantDiagram

/-!
概要：全単位族の終端を、元の余錐頂点の評価の後の定値図式として表示する。
方針：定値写像による前合成と元の頂点での評価を、展開した全族で比較する。
規約：全次数の厳密な等式。使われ方：単位三角柱の余極限側の全三角形。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 定値写像による前合成は、元の頂点で評価した後の定値関手族そのもの。 -/
lemma pre_const_eq_evaluate_constant {K J X : SSet.{u}} (v : J _⦋0⦌) :
    (pre (SSet.const v : K ⟶ J)).app X = evaluateFunctorAt v ≫ constantDiagram K X := by
  apply uncurry_injective
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro p
  change p.2.app n (𝟙 n) (PinchedHom.constant v n.unop.len) =
    X.map (𝟙 n) (p.2.app n (𝟙 n) (PinchedHom.constant v n.unop.len))
  rw [CategoryTheory.Functor.map_id_apply]

/-- 全単位族は終端で元の頂点評価の後の定値図式に厳密に一致する。 -/
lemma coconeUnitFamily_one_constant {K X T : SSet.{u}}
    (q : T ⟶ (ihom (join K (Δ[0] : SSet.{u}))).obj X) :
    SSet.ι₁ ≫ coconeUnitFamily q = q ≫
      evaluateFunctorAt (SSet.yonedaEquiv (joinInr K (Δ[0] : SSet.{u}))) ≫
        constantDiagram K X := by
  rw [coconeUnitFamily_one, pre_const_eq_evaluate_constant]

/-- 任意の全図式族を、同じ余極限単位により元の余極限族の定値図式へ結ぶ全円柱。 -/
def coherentColimitUnitParameterHomotopy (B : SSet.{u}) {P : SSet.{u + 1}}
    (t : P ⟶ (ihom ((SSet.uliftFunctor.{u + 1, u}).obj B)).obj SpaceInfinity.{u}) :
    SSet.Homotopy t (t ≫ coherentColimitFunctor B ≫
      constantDiagram ((SSet.uliftFunctor.{u + 1, u}).obj B) SpaceInfinity.{u}) where
  h := (t ▷ Δ[1]) ≫ coherentColimitUnitFamily B
  h₀ := by
    rw [← Category.assoc, SSet.ι₀_comp, Category.assoc]
    change t ≫ (SSet.ι₀ ≫ coconeUnitFamily (coherentColimitCoconeFunctor B)) = _
    rw [coconeUnitFamily_zero, coherentColimitCoconeFunctor_restrict, Category.comp_id]
    rfl
  h₁ := by
    rw [← Category.assoc, SSet.ι₁_comp, Category.assoc]
    change t ≫ (SSet.ι₁ ≫ coconeUnitFamily (coherentColimitCoconeFunctor B)) = _
    rw [coconeUnitFamily_one_constant]
    rfl
  rel := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro p
    exact False.elim p.1.property

end SerrePositivity.InfinityCategories.F2
