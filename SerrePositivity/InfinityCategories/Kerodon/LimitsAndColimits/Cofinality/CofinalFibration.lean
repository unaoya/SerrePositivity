module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.CofinalFiberContraction
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.RightFibrationContractible
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.LeftPrism

/-!
概要：cofinal な左右 fibration は trivial Kan fibration。
方針：right 側は可縮な Kan fiber、left 側は底上の逆向き収縮と prism を使う。
規約：底の quasicategory 性は不要。全境界の厳密な持ち上げを結論する。
使われ方：Kerodon Corollary 7.2.1.14（Tag 02ND）、cofinality の anodyne 因子への還元。

対応節は Kerodon 7.2（Tag 02MZ）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality

/-- 概要：底上の収縮を持つ right fibration は全境界を持ち上げる。
方針：各 fiber の Kan 性と収縮を Core の可縮 fiber の判定へ渡す。
規約：底は任意の単体集合。
使われ方：cofinal right fibration の判定。 -/
lemma CofinalSectionHomotopy.trivialKanFibration_of_rightFibration
    {E B : SSet.{u}} {p : E ⟶ B} [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration p] (d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.CofinalSectionHomotopy p) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration p := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.rightFibration_trivialKanFibration_of_contractible_fibers p
  intro b
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_kanComplex p b
  exact d.fiber_isContractibleKan b

/-- 概要：底上の両方向の収縮を持つ left fibration は全境界を持ち上げる。
方針：切断で充填した単体を、境界上の収縮に沿う prism の持ち上げで補正する。
規約：底は任意で、境界の元の持ち上げを厳密に復元する。
使われ方：cofinal left fibration の判定。 -/
lemma CofinalSectionHomotopy.trivialKanFibration_of_leftFibration
    {E B : SSet.{u}} {p : E ⟶ B} [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] (d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.CofinalSectionHomotopy p) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration p := by
  let s := d.sectionMap
  have hs : s ≫ p = 𝟙 B := d.section_comp
  let J := (β_ (Δ[1] : SSet.{u}) E).hom ≫ d.reverseHomotopy.h
  have hJ₀ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 E ≫ J = p ≫ s := by
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.prismEndpoint_zero_braiding]
    exact d.reverseHomotopy.h₀
  have hJ₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 E ≫ J = 𝟙 E := by
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.prismEndpoint_one_braiding]
    exact d.reverseHomotopy.h₁
  have hJp : J ≫ p = snd (Δ[1] : SSet.{u}) E ≫ p := by
    rw [Category.assoc, d.reverseHomotopy_comp,
      ← Category.assoc]
    rfl
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.trivialKanFibration_iff_boundary _).2
  intro n
  constructor
  intro a b sq
  let H := (Δ[1] ◁ a) ≫ J
  let F₀ := b ≫ s
  let b' := snd (Δ[1] : SSet.{u}) (Δ[n] : SSet.{u}) ≫ b
  have hF₀ : (boundary n).ι ≫ F₀ = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 (boundary n : SSet.{u}) ≫ H := by
    dsimp only [F₀, H]
    rw [← Category.assoc (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 (boundary n : SSet.{u})) (Δ[1] ◁ a) J,
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint_naturality, Category.assoc, hJ₀]
    rw [← Category.assoc, ← sq.w, Category.assoc]
  have hH : H ≫ p = (Δ[1] ◁ (boundary n).ι) ≫ b' := by
    rw [Category.assoc, hJp]
    change ((Δ[1] : SSet.{u}) ◁ a) ≫ snd Δ[1] E ≫ p =
      (Δ[1] ◁ (boundary n).ι) ≫ snd Δ[1] Δ[n] ≫ b
    rw [← Category.assoc, whiskerLeft_snd, Category.assoc,
      ← Category.assoc (Δ[1] ◁ (boundary n).ι), whiskerLeft_snd, Category.assoc, sq.w]
  have hb : F₀ ≫ p = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 Δ[n] ≫ b' := by
    change (b ≫ s) ≫ p = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 Δ[n] ≫ (snd Δ[1] Δ[n] ≫ b)
    rw [Category.assoc, hs, Category.comp_id, ← Category.assoc]
    rfl
  obtain ⟨F, hF, _, hFp⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.leftFibration_lift_boundary_prism p n H F₀ b' hF₀ hH hb
  refine CommSq.HasLift.mk' { l := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 Δ[n] ≫ F, fac_left := ?_, fac_right := ?_ }
  · rw [← Category.assoc (boundary n).ι (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 Δ[n]) F,
      ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint_naturality, Category.assoc, hF]
    change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (boundary n : SSet.{u}) ≫ (Δ[1] ◁ a) ≫ J = a
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint_naturality, Category.assoc, hJ₁, Category.comp_id]
  · rw [Category.assoc, hFp]
    change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 Δ[n] ≫ (snd Δ[1] Δ[n] ≫ b) = b
    rw [← Category.assoc]
    rfl

/-- 概要：right cofinal な right fibration は trivial Kan fibration。
方針：相対関手空間の同値から底上の両方向の収縮を得て、全境界の判定を適用する。
規約：元の二対象に quasicategory 性を課さない。
使われ方：Kerodon Corollary 7.2.1.14（Tag 02ND） の fibration への還元後。 -/
lemma IsRightCofinal.trivialKanFibration {E B : SSet.{u}} {p : E ⟶ B}
    [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration p] (hp : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.IsRightCofinal p) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration p := by
  obtain ⟨d⟩ := hp.nonempty_sectionHomotopy
  exact d.trivialKanFibration_of_rightFibration

/-- 概要：left cofinal な left fibration は trivial Kan fibration。
方針：相対関手空間の同値から底上の両方向の収縮を得て、全境界の判定を適用する。
規約：元の二対象に quasicategory 性を課さない。
使われ方：Kerodon Corollary 7.2.1.14（Tag 02ND） の fibration への還元後。 -/
lemma IsLeftCofinal.trivialKanFibration {E B : SSet.{u}} {p : E ⟶ B}
    [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] (hp : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.IsLeftCofinal p) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration p := by
  obtain ⟨d⟩ := hp.nonempty_sectionHomotopy
  exact d.trivialKanFibration_of_leftFibration

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality
