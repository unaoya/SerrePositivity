module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.CofinalFunctorOverPre

/-!
概要：底上のホモトピーの、相対関手空間の前合成への作用。
方針：パラメータ付きの評価をホモトピーで前合成し、同じ底の fiber へ戻す。
規約：元の空間や関手空間の Kan 性を必要としない。
使われ方：底上のホモトピー逆から cofinality を得る。

対応節は Kerodon 7.2（Tag 02MZ）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality

/-- 概要：底上で結ばれた二つの射は相対関手空間の前合成でもホモトピック。
方針：関手の族を H で前合成して評価し、底の条件で相対 curry を取る。
規約：H の底への像は区間に依存しないという厳密な等式。
使われ方：trivial Kan fibration に沿う相対前合成のホモトピー逆。 -/
def cofinalFunctorOverPreHomotopy {E B : SSet.{u}} (p : E ⟶ B) {a b : Over B}
    (i j : a ⟶ b) (H : SSet.Homotopy i.left j.left)
    (hH : H.h ≫ b.hom = fst a.left (Δ[1] : SSet.{u}) ≫ a.hom) :
    SSet.Homotopy (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.cofinalFunctorOverPre p i) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.cofinalFunctorOverPre p j) := by
  let U := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.cofinalFunctorSpace p b.hom
  let pos : a.left ⊗ (U ⊗ (Δ[1] : SSet.{u})) ⟶ a.left ⊗ (Δ[1] : SSet.{u}) :=
    lift (fst _ _) (snd _ _ ≫ snd _ _)
  let c : a.left ⊗ (U ⊗ (Δ[1] : SSet.{u})) ⟶ b.left ⊗ U :=
    lift (pos ≫ H.h) (snd _ _ ≫ fst _ _)
  let F := c ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cofinalFunctorUncurry (𝟙 U)
  have hF : F ≫ p = fst a.left (U ⊗ (Δ[1] : SSet.{u})) ≫ a.hom := by
    rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cofinalFunctorUncurry_projection, ← Category.assoc, lift_fst,
      Category.assoc, hH, ← Category.assoc, lift_fst]
  let L := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cofinalFunctorCurry (p := p) (a := a.hom) F hF
  have hc₀ : (a.left ◁ SSet.ι₀) ≫ c = i.left ▷ U := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro z
    apply Prod.ext
    · exact ConcreteCategory.congr_hom (NatTrans.congr_app H.h₀ n) z.1
    · rfl
  have hc₁ : (a.left ◁ SSet.ι₁) ≫ c = j.left ▷ U := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro z
    apply Prod.ext
    · exact ConcreteCategory.congr_hom (NatTrans.congr_app H.h₁ n) z.1
    · rfl
  refine { h := L, h₀ := ?_, h₁ := ?_, rel := ?_ }
  · change SSet.ι₀ ≫ L = _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.cofinalFunctorOverPre p i
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_hom_ext ((ihom a.left).map p) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex a.hom)
    dsimp only [L, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cofinalFunctorCurry]
    rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift_ι, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.cofinalFunctorOverPre_ι]
    apply uncurry_injective
    rw [uncurry_natural_left, uncurry_curry, uncurry_pre_app]
    change (a.left ◁ SSet.ι₀) ≫ (c ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cofinalFunctorUncurry (𝟙 U)) =
      (i.left ▷ U) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cofinalFunctorUncurry (𝟙 U)
    rw [← Category.assoc, hc₀]
  · change SSet.ι₁ ≫ L = _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.cofinalFunctorOverPre p j
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_hom_ext ((ihom a.left).map p) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex a.hom)
    dsimp only [L, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cofinalFunctorCurry]
    rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift_ι, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.cofinalFunctorOverPre_ι]
    apply uncurry_injective
    rw [uncurry_natural_left, uncurry_curry, uncurry_pre_app]
    change (a.left ◁ SSet.ι₁) ≫ (c ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cofinalFunctorUncurry (𝟙 U)) =
      (j.left ▷ U) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cofinalFunctorUncurry (𝟙 U)
    rw [← Category.assoc, hc₁]
  · apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro z
    exact False.elim z.1.property

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality
