module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TetrahedronFamilyVertices

/-!
概要：区間同型で移した全族を元の始域で評価すると、同じ入力点の元の全族へ戻る。
方針：uncurry の前合成則と同型の厳密逆を使う。
規約：全次数の射の等号。
使われ方：再構成二胞体の全 native 区間を元の長 Hom へ戻す。

対応節は Kerodon 7.1（Tag 02H1）。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits

lemma triangleIntervalIsoEvaluation {A B P H : SSet.{u}} (e : A ≅ B)
    (q : P ⟶ (ihom A).obj H) (p : P _⦋0⦌) :
    lift e.hom (SSet.const p) ≫ uncurry (q ≫ (pre e.inv).app H) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.familyAtVertex (uncurry q) p := by
  rw [uncurry_pre_app, ← Category.assoc]
  have h : lift e.hom (SSet.const p) ≫ (e.inv ▷ P) = lift (𝟙 A) (SSet.const p) := by
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro a
    apply Prod.ext
    · exact ConcreteCategory.congr_hom (NatTrans.congr_app e.hom_inv_id d) a
    · rfl
  rw [h]
  rfl

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
