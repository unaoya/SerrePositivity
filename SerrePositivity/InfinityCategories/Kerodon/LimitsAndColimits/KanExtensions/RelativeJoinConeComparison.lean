module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ConeContraction
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RelativeJoinLocalCone

/-!
概要：錐の底の指定ホモトピーと整合する相対 join 内の余錐の比較を構成する。
方針：底の円柱に頂点を付け、錐を縮める係数と合わせて相対 join へ持ち上げる。
規約：持ち上げを実際に構成し、四境界だけから存在を仮定しない。
使われ方：comma の fiber の余錐と元の局所余錐を比較する。

対応節は Kerodon 7.3（Tag 02Y1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions

/-- 概要：底の円柱と錐の標準変換が一致すれば相対 join 内の錐の比較を構成できる。
方針：円柱の底に頂点を付けた join を相対 join へ持ち上げ、直積比較を前合成する。
規約：底のホモトピーの時間を第一因子へ移す。
使われ方：図式と頂点を固定した局所余錐の比較。 -/
def kanRelativeJoinConeComparison {A E C : SSet.{u}} (p : E ⟶ C)
    {a₀ a₁ : A ⟶ E} (R : SSet.Homotopy a₀ a₁)
    (F : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join A (Δ[0] : SSet.{u}) ⟶ C) (b : (Δ[0] : SSet.{u}) ⟶ C)
    (hR : (β_ (Δ[1] : SSet.{u}) A).hom ≫ R.h ≫ p = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.rightMappingSpacePrism A ≫ F)
    (hB : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr A Δ[0] ≫ F = b) :
    (Δ[1] : SSet.{u}) ⊗ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join A Δ[0] ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoin p (𝟙 C) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinTensorLeft Δ[1] A Δ[0] ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeJoinLift p (𝟙 C)
    ((β_ (Δ[1] : SSet.{u}) A).hom ≫ R.h) b (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coneContractionCore A ≫ F)
    (by rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coneContractionCore_inl]; exact hR.symm)
    (by rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coneContractionCore_inr, hB, Category.comp_id])

/-- 概要：比較の始点は元の錐を相対 join へ持ち上げたもの。
方針：直積比較の時間零と、底のホモトピーと係数の零境界。
規約：元の錐の底の条件を明示する。
使われ方：比較元の局所余錐の同定。 -/
lemma kanRelativeJoinConeComparison_zero {A E C : SSet.{u}} (p : E ⟶ C)
    {a₀ a₁ : A ⟶ E} (R : SSet.Homotopy a₀ a₁)
    (F : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join A (Δ[0] : SSet.{u}) ⟶ C) (b : (Δ[0] : SSet.{u}) ⟶ C)
    (hR : (β_ (Δ[1] : SSet.{u}) A).hom ≫ R.h ≫ p = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.rightMappingSpacePrism A ≫ F)
    (hB : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr A Δ[0] ≫ F = b) (hA : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl A Δ[0] ≫ F = a₀ ≫ p) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join A (Δ[0] : SSet.{u})) ≫
      kanRelativeJoinConeComparison p R F b hR hB =
        _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeJoinLift p (𝟙 C) a₀ b F hA (by rw [hB, Category.comp_id]) := by
  rw [kanRelativeJoinConeComparison, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.stable_joinTensorLeft_prismEndpoint,
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeJoinLift_precomp]
  have ha : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 A ≫ ((β_ (Δ[1] : SSet.{u}) A).hom ≫ R.h) = a₀ := by
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.prismEndpoint_zero_braiding, R.h₀]
  have hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 A) (𝟙 (Δ[0] : SSet.{u})) ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coneContractionCore A ≫ F) = F := by
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coneContractionCore_zero, Category.id_comp]
  simp only [ha, hf, Category.id_comp]

/-- 概要：比較の終点は底のホモトピーの終点と定値の底の係数で表される錐。
方針：直積比較の時間一と底のホモトピーの終点を計算する。
規約：終点の底の定値条件を明示する。
使われ方：comma fiber 内の余錐との同定。 -/
lemma kanRelativeJoinConeComparison_one {A E C : SSet.{u}} (p : E ⟶ C)
    {a₀ a₁ : A ⟶ E} (R : SSet.Homotopy a₀ a₁)
    (F : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join A (Δ[0] : SSet.{u}) ⟶ C) (b : (Δ[0] : SSet.{u}) ⟶ C)
    (hR : (β_ (Δ[1] : SSet.{u}) A).hom ≫ R.h ≫ p = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.rightMappingSpacePrism A ≫ F)
    (hB : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr A Δ[0] ≫ F = b)
    (hA : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl A Δ[0] ≫
      ((SSet.const (stdSimplex.obj₀Equiv.symm 0)) ≫ b) = a₁ ≫ p) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join A (Δ[0] : SSet.{u})) ≫
      kanRelativeJoinConeComparison p R F b hR hB =
        _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeJoinLift p (𝟙 C) a₁ b
          ((SSet.const (stdSimplex.obj₀Equiv.symm 0)) ≫ b) hA (by
            rw [← Category.assoc, SSet.comp_const, Category.comp_id]
            have he : (SSet.const (stdSimplex.obj₀Equiv.symm 0) :
                (Δ[0] : SSet.{u}) ⟶ Δ[0]) = 𝟙 _ := stdSimplex.isTerminalObj₀.hom_ext _ _
            rw [he, Category.id_comp]) := by
  rw [kanRelativeJoinConeComparison, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.stable_joinTensorLeft_prismEndpoint,
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeJoinLift_precomp]
  have ha : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 A ≫ ((β_ (Δ[1] : SSet.{u}) A).hom ≫ R.h) = a₁ := by
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.prismEndpoint_one_braiding, R.h₁]
  have hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 A) (𝟙 (Δ[0] : SSet.{u})) ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coneContractionCore A ≫ F) = SSet.const (stdSimplex.obj₀Equiv.symm 0) ≫ b := by
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coneContractionCore_one, Category.assoc, hB]
  simp only [ha, hf, Category.id_comp]

/-- 概要：比較の底側は指定された底の円柱を相対 join の左端へ入れたもの。
方針：直積と join の比較の左境界と相対 join の持ち上げの左境界。
規約：底の指定変換を raw な射として保持する。
使われ方：図式 F₀ の固定条件の確認。 -/
lemma kanRelativeJoinConeComparison_inl {A E C : SSet.{u}} (p : E ⟶ C)
    {a₀ a₁ : A ⟶ E} (R : SSet.Homotopy a₀ a₁)
    (F : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join A (Δ[0] : SSet.{u}) ⟶ C) (b : (Δ[0] : SSet.{u}) ⟶ C)
    (hR : (β_ (Δ[1] : SSet.{u}) A).hom ≫ R.h ≫ p = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.rightMappingSpacePrism A ≫ F)
    (hB : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr A Δ[0] ≫ F = b) :
    ((Δ[1] : SSet.{u}) ◁ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl A Δ[0]) ≫ kanRelativeJoinConeComparison p R F b hR hB =
      (β_ (Δ[1] : SSet.{u}) A).hom ≫ R.h ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinInl p (𝟙 C) := by
  rw [kanRelativeJoinConeComparison, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinTensorLeft_inl,
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeJoinLift_inl]
  exact Category.assoc _ _ _

/-- 概要：比較の頂点は全時間で同じ右端に固定される。
方針：直積と join の比較の右境界と相対 join の持ち上げの右境界。
規約：頂点の像は b。
使われ方：比較が頂点を固定した余錐のホモトピーであることの確認。 -/
lemma kanRelativeJoinConeComparison_inr {A E C : SSet.{u}} (p : E ⟶ C)
    {a₀ a₁ : A ⟶ E} (R : SSet.Homotopy a₀ a₁)
    (F : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join A (Δ[0] : SSet.{u}) ⟶ C) (b : (Δ[0] : SSet.{u}) ⟶ C)
    (hR : (β_ (Δ[1] : SSet.{u}) A).hom ≫ R.h ≫ p = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.rightMappingSpacePrism A ≫ F)
    (hB : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr A Δ[0] ≫ F = b) :
    ((Δ[1] : SSet.{u}) ◁ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr A Δ[0]) ≫ kanRelativeJoinConeComparison p R F b hR hB =
      snd (Δ[1] : SSet.{u}) Δ[0] ≫ b ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinInr p (𝟙 C) := by
  rw [kanRelativeJoinConeComparison, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinTensorLeft_inr,
    Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeJoinLift_inr]

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions
