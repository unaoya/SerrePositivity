module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.TerminalHomotopyAnodyne
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.CofinalFixedPrism
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.PrismLastContraction

/-!
概要：標準単体上の left fibration の終点 fiber の包含は right anodyne。
方針：底の終点への収縮を、終点 fiber を全時間で固定して持ち上げる。
規約：底は標準単体。一般の cocartesian fibration の pullback 安定性は別工程。
使われ方：Kerodon Example 7.2.3.12（Tag 03J8） の left fibration・標準単体の場合。

対応節は Kerodon 7.2（Tag 02MZ）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality

/-- 概要：頂点 fiber の包含は単射。
方針：各次数の部分型の値への射の単射性を使う。
規約：fibration 性は不要。
使われ方：終点 fiber の包含との pushout-product。 -/
instance cofinalVertexFiberι_mono {E B : SSet.{u}} (p : E ⟶ B) (b : B _⦋0⦌) :
    Mono (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p b) := by
  rw [NatTrans.mono_iff_mono_app]
  intro n
  rw [mono_iff_injective]
  exact Subtype.val_injective

/-- 概要：終点に定値な図式は標準単体の終点収縮で動かない。
方針：時刻零と一の両方の分岐が同じ最後の頂点を与えることを検査する。
規約：パラメータ A は任意。
使われ方：終点 fiber を固定した prism の底の可換性。 -/
lemma cofinalPrismLastContraction_const (n : ℕ) (A : SSet.{u}) :
    (Δ[1] ◁ (SSet.const (stdSimplex.obj₀Equiv.symm (Fin.last n)) : A ⟶ Δ[n])) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.prismLastContraction n = SSet.const (stdSimplex.obj₀Equiv.symm (Fin.last n)) := by
  apply SSet.hom_ext
  rintro ⟨⟨m⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨t, a⟩
  apply stdSimplex.ext
  intro k
  change (if _ = 0 then Fin.last n else Fin.last n) = Fin.last n
  split_ifs <;> rfl

/-- 概要：固定した頂点への収縮を持つ底の left fibration では、その fiber の包含は right anodyne。
方針：底の収縮を fiber を固定して持ち上げ、比較射を pushout-product の retract にする。
規約：hCfix は頂点に定値な任意のパラメータ族を固定する条件。底の充填性は不要。
使われ方：標準単体と外側ホーンの終点 fiber による計算の共通部分。 -/
lemma leftFibration_terminalFiber_rightAnodyne_of_fixed_contraction
    {E B : SSet.{u}} (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] (b : B _⦋0⦌)
    (C : (Δ[1] : SSet.{u}) ⊗ B ⟶ B)
    (hC₀ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 B ≫ C = 𝟙 B)
    (hC₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 B ≫ C = SSet.const b)
    (hCfix : ∀ K : SSet.{u}, (Δ[1] ◁ (SSet.const b : K ⟶ B)) ≫ C = SSet.const b) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.rightAnodyneExtensions (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p b) := by
  let F := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p b
  let i := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p b
  let β := (Δ[1] ◁ p) ≫ C
  let G := snd (Δ[1] : SSet.{u}) F ≫ i
  have h₀ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 F ≫ G = i ≫ 𝟙 E := by
    rw [Category.comp_id]
    rfl
  have hG : G ≫ p = (Δ[1] ◁ i) ≫ β := by
    change (snd (Δ[1] : SSet.{u}) F ≫ i) ≫ p =
      (Δ[1] ◁ i) ≫ ((Δ[1] ◁ p) ≫ C)
    rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι_comp, SSet.comp_const, ← Category.assoc,
      ← MonoidalCategory.whiskerLeft_comp, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι_comp,
      hCfix]
  have hβ : (𝟙 E) ≫ p = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 E ≫ β := by
    rw [Category.id_comp]
    change p = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 E ≫ (Δ[1] ◁ p) ≫ C
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint_naturality, Category.assoc,
      hC₀, Category.comp_id]
  obtain ⟨H, hfix, hH₀, hHp⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.leftFibration_lift_fixed_prism i p G (𝟙 E) β h₀ hG hβ
  let L := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 E ≫ H
  have hL : L ≫ p = SSet.const b := by
    rw [Category.assoc, hHp]
    change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 E ≫ (Δ[1] ◁ p) ≫ C = SSet.const b
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint_naturality, Category.assoc,
      hC₁, SSet.comp_const]
  let r := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift p b L hL
  have hir : i ≫ r = 𝟙 F := by
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_hom_ext p b
    rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift_ι, Category.id_comp]
    change i ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 E ≫ H = i
    rw [← Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint_naturality, Category.assoc, hfix]
    rfl
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.rightAnodyneExtensions_of_fixed_terminal_homotopy i r hir H hH₀
  · exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift_ι p b L hL).symm
  · exact hfix

/-- 概要：left fibration の標準単体の終点 fiber の包含は right anodyne。
方針：標準単体の終点収縮を、fiber を固定した収縮の一般補題へ渡す。
規約：全空間の quasicategory 性は別に仮定しない。次数零も含む。
使われ方：Kerodon Example 7.2.3.12（Tag 03J8） の標準単体の場合。 -/
lemma leftFibration_terminalFiber_rightAnodyne {E : SSet.{u}} {n : ℕ}
    (p : E ⟶ (Δ[n] : SSet.{u})) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.rightAnodyneExtensions (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p (stdSimplex.obj₀Equiv.symm (Fin.last n))) :=
  leftFibration_terminalFiber_rightAnodyne_of_fixed_contraction p _ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.prismLastContraction n)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.prismLastContraction_zero n) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.prismLastContraction_one n)
    (cofinalPrismLastContraction_const n)

/-- 概要：left fibration の標準単体の終点 fiber の包含は right cofinal。
方針：元の包含の right anodyne 性を cofinality の十分性に渡す。
規約：この時点では一般の底の終対象の場合は主張しない。
使われ方：right cofinality の pullback 計算の基礎となる終点の場合。 -/
lemma leftFibration_terminalFiber_isRightCofinal {E : SSet.{u}} {n : ℕ}
    (p : E ⟶ (Δ[n] : SSet.{u})) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.IsRightCofinal (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p (stdSimplex.obj₀Equiv.symm (Fin.last n))) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.isRightCofinal_of_rightAnodyne _ (leftFibration_terminalFiber_rightAnodyne p)

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality
