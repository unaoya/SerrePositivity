module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.WeightedSectionParameter
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.UniverseSections
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.OrderDiagrams

/-!
概要：BK end の元の点の全切断を、各初区間の元の係数で計算する。
方針：単位パラメータの直積を右単位子で除き、普遍評価とその点での評価を比較する。
規約：全次数を保持し、Kan 性を要求しない。使われ方：companion の錐全体の具体計算。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u v
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Spectra.BousfieldKanPointSection
variable {I : Type u} [SmallCategory I] {H : I ⥤ SSet.{u}}

/-- 単位パラメータの点に対応する、元の重み上の全切断。 -/
def transform (p : (𝟙_ SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanHolim H) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight I ⟶ H :=
  (ρ_ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight I)).inv ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsUncurry p

/-- 普遍的な weighted nerve の族を、元の単位パラメータの点で評価した切断。 -/
def sectionMap (p : (𝟙_ SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanHolim H) :
    nerve I ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerve H :=
  (ρ_ (nerve I)).inv ≫ (nerve I ◁ p) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeightedNerveEvaluation H

/-- 元の点のパラメータ係数は、同じ全切断の初区間への制限に厳密一致する。 -/
lemma coefficients (p : (𝟙_ SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanHolim H) {n : ℕ}
    (σ : ComposableArrows I n) (a : (Δ[n] : SSet.{u}) ⟶ 𝟙_ SSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveCoefficients (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsUncurry p) σ a =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.prefixOverWeight σ ≫ Functor.whiskerLeft σ (transform p) := by
  apply NatTrans.ext
  funext j
  change lift ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.prefixOverWeight σ).app j)
      (stdSimplex.map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixInclusion j.val n (Nat.le_of_lt_succ j.isLt)) ≫ a) ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsUncurry p).app (σ.obj j) =
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.prefixOverWeight σ).app j ≫
      (ρ_ ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight I).obj (σ.obj j))).inv ≫
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsUncurry p).app (σ.obj j)
  have h : lift ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.prefixOverWeight σ).app j)
      (stdSimplex.map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixInclusion j.val n (Nat.le_of_lt_succ j.isLt)) ≫ a) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.prefixOverWeight σ).app j ≫
        (ρ_ ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight I).obj (σ.obj j))).inv := by
    apply CartesianMonoidalCategory.hom_ext
    · rw [lift_fst, Category.assoc]
      rfl
    · exact Subsingleton.elim _ _
  rw [h, Category.assoc]

/-- 元の点の weighted nerve 切断の全単体は、同じ初区間と全切断の係数を持つ。 -/
lemma sectionMap_app (p : (𝟙_ SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanHolim H) {n : ℕ}
    (σ : ComposableArrows I n) :
    (sectionMap p).app (Opposite.op ⦋n⦌) σ =
      ⟨σ, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.prefixOverWeight σ ≫ Functor.whiskerLeft σ (transform p)⟩ := by
  unfold sectionMap
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanSectionHomEquiv_apply]
  change (⟨σ, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveCoefficients (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsUncurry p) σ
    (SSet.yonedaEquiv.symm PUnit.unit)⟩ : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveSimplex H n) = _
  rw [coefficients]

/-- 持ち上げた点のパラメータを評価する射は、元の単位パラメータの評価の ULift。 -/
lemma liftedParameter (p : (𝟙_ SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanHolim H) :
    inv (fst ((SSet.uliftFunctor.{v, u}).obj (nerve I)) (Δ[0] : SSet.{max u v})) ≫
      ((SSet.uliftFunctor.{v, u}).obj (nerve I) ◁
        SSet.yonedaEquiv.symm (ULift.up (SSet.unitHomEquiv _ p))) ≫
      (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftTensorIso (nerve I) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanHolim H)).inv =
    (SSet.uliftFunctor.{v, u}).map ((ρ_ (nerve I)).inv ≫ (nerve I ◁ p)) := by
  have hf : inv (fst ((SSet.uliftFunctor.{v, u}).obj (nerve I))
      (Δ[0] : SSet.{max u v})) =
      lift (𝟙 _) (SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 1))) := by
    apply (cancel_mono (fst _ _)).mp
    rw [IsIso.inv_hom_id, lift_fst]
  rw [hf]
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro σ
  change ULift.up (σ.down, _) = ULift.up (σ.down, _)
  congr 1
  exact Prod.ext rfl (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.unitHom_app_constant p n).symm

/-- 宇宙を持ち上げた元の点の weighted 切断も、同じ元の切断の ULift に厳密一致する。 -/
lemma liftedSection (p : (𝟙_ SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanHolim H) :
    inv (fst ((SSet.uliftFunctor.{v, u}).obj (nerve I)) (Δ[0] : SSet.{max u v})) ≫
      ((SSet.uliftFunctor.{v, u}).obj (nerve I) ◁
        SSet.yonedaEquiv.symm (ULift.up (SSet.unitHomEquiv _ p))) ≫
      (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftTensorIso (nerve I) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanHolim H)).inv ≫
      (SSet.uliftFunctor.{v, u}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeightedNerveEvaluation H) =
    (SSet.uliftFunctor.{v, u}).map (sectionMap p) := by
  have h := congrArg (fun f ↦ f ≫ (SSet.uliftFunctor.{v, u}).map
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeightedNerveEvaluation H)) (liftedParameter.{u, v} p)
  simp only [Category.assoc] at h
  exact h.trans ((SSet.uliftFunctor.{v, u}).map_comp _ _).symm

end SerrePositivity.KST.Spectra.BousfieldKanPointSection
