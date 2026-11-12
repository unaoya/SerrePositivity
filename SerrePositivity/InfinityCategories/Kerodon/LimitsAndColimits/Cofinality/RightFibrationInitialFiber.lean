module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.InitialFixedContraction
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.CofinalFixedRightPrism
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.TerminalFiberCofinality
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.WeakHomotopyInverse

/-!
概要：right fibration の始対象上の fiber の包含は単体的ホモトピー同値。
方針：始対象を固定した底の収縮を、fiber を固定して終端から持ち上げる。
規約：底の quasicategory 性は不要。始対象性は境界充填の定義で受け取る。
使われ方：Quillen A の十分性で coslice 引き戻しと頂点 fiber を比較する。

対応節は Kerodon 7.2（Tag 02MZ）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality

/-- 概要：right fibration の始対象上の fiber 包含は実際の単体的ホモトピー逆を持つ。
方針：固定した初期収縮を持ち上げ、その時刻零を fiber に持ち上げて逆射にする。
規約：元の二対象に Kan 性を要求しない。
使われ方：弱可縮な coslice 引き戻しから Kan fiber の弱可縮性を得る。 -/
lemma rightFibration_initialFiber_isSimplicialHomotopyEquivalence {E B : SSet.{u}}
    (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration p] (b : B _⦋0⦌) (hb : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsInitialVertex b) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p b) := by
  obtain ⟨C, hC₀, hC₁, hCfix⟩ := hb.exists_fixed_initial_prism
  let F := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p b
  let i := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p b
  let G := snd (Δ[1] : SSet.{u}) F ≫ i
  let β := (Δ[1] ◁ p) ≫ C
  have h₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 F ≫ G = i ≫ 𝟙 E := by
    rw [Category.comp_id]
    rfl
  have hG : G ≫ p = (Δ[1] ◁ i) ≫ β := by
    change (snd (Δ[1] : SSet.{u}) F ≫ i) ≫ p =
      (Δ[1] ◁ i) ≫ ((Δ[1] ◁ p) ≫ C)
    rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι_comp, SSet.comp_const, ← Category.assoc,
      ← MonoidalCategory.whiskerLeft_comp, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι_comp, hCfix]
  have hβ : (𝟙 E) ≫ p = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 E ≫ β := by
    rw [Category.id_comp]
    change p = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 E ≫ (Δ[1] ◁ p) ≫ C
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint_naturality, Category.assoc, hC₁, Category.comp_id]
  obtain ⟨H, hfix, hH₁, hHp⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.rightFibration_lift_fixed_prism i p G (𝟙 E) β h₁ hG hβ
  let L := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 E ≫ H
  have hL : L ≫ p = SSet.const b := by
    rw [Category.assoc, hHp]
    change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 E ≫ (Δ[1] ◁ p) ≫ C = SSet.const b
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint_naturality, Category.assoc, hC₀, SSet.comp_const]
  let r := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift p b L hL
  have hir : i ≫ r = 𝟙 F := by
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_hom_ext p b
    rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift_ι, Category.id_comp]
    change i ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 E ≫ H = i
    rw [← Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint_naturality, Category.assoc, hfix]
    rfl
  have K : SSet.Homotopy (r ≫ i) (𝟙 E) := by
    refine { h := (β_ E (Δ[1] : SSet.{u})).hom ≫ H, h₀ := ?_, h₁ := ?_, rel := ?_ }
    · change (SSet.ι₀ ≫ (β_ E (Δ[1] : SSet.{u})).hom) ≫ H = r ≫ i
      change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 E ≫ H = r ≫ i
      exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift_ι p b L hL).symm
    · change (SSet.ι₁ ≫ (β_ E (Δ[1] : SSet.{u})).hom) ≫ H = 𝟙 E
      exact hH₁
    · apply SSet.hom_ext
      intro n
      apply ConcreteCategory.hom_ext
      intro s
      exact False.elim s.1.property
  refine ⟨r, ?_, ⟨K⟩⟩
  rw [hir]
  exact ⟨SSet.RelativeMorphism.Homotopy.refl (SSet.RelativeMorphism.botEquiv.symm (𝟙 F))⟩

/-- 概要：right fibration の始対象上の fiber 包含は弱ホモトピー同値。
方針：構成した実際のホモトピー逆を全 Kan 標的への検査に移す。
規約：底や全空間の Kan 性は不要。
使われ方：Quillen A の right fibration の場合の十分性。 -/
lemma rightFibration_initialFiber_isWeakHomotopyEquivalence {E B : SSet.{u}}
    (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration p] (b : B _⦋0⦌) (hb : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsInitialVertex b) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p b) :=
  (rightFibration_initialFiber_isSimplicialHomotopyEquivalence p b hb).isWeakHomotopyEquivalence

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality
