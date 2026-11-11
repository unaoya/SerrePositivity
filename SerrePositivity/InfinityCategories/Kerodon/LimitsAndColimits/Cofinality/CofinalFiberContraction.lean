module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.CofinalSectionHomotopy
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.ContractibleHomotopyRetract
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.WeakContractibility

/-!
概要：底上の収縮を各頂点 fiber に制限する。
方針：切断で fiber の基点を取り、底に定値な円柱をその fiber へ持ち上げる。
規約：この制限の構成には fibration 性は不要。可縮 Kan 性には fiber の Kan 性を使う。
使われ方：cofinal な fibration の全境界充填を fiber ごとに検出する。

対応節は Kerodon 7.2（Tag 02MZ）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality

/-- 概要：底上の切断が指定する fiber の基点。
方針：切断の頂点への作用に、底への合成が元の頂点である条件を添える。
規約：頂点 b は任意。
使われ方：fiber の定値自己写像の値。 -/
def CofinalSectionHomotopy.fiberPoint {E B : SSet.{u}} {p : E ⟶ B}
    (d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.CofinalSectionHomotopy p) (b : B _⦋0⦌) : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p b) _⦋0⦌ :=
  ⟨d.sectionMap.app (Opposite.op ⦋0⦌) b, by
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_zero]
    exact ConcreteCategory.congr_hom (NatTrans.congr_app d.section_comp (Opposite.op ⦋0⦌)) b⟩

/-- 概要：底上の収縮は各 fiber 内の恒等写像から定値写像への収縮を与える。
方針：円柱の底への像が定値であることにより vertexFiber へ持ち上げる。
規約：始域と標的は同じ fiber、区間は第二因子。
使われ方：Kan fiber を可縮と結論する明示的なホモトピー。 -/
def CofinalSectionHomotopy.fiberContraction {E B : SSet.{u}} {p : E ⟶ B}
    (d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.CofinalSectionHomotopy p) (b : B _⦋0⦌) :
    SSet.Homotopy (𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p b)) (SSet.const (d.fiberPoint b)) := by
  let ι := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p b
  let H := (ι ▷ (Δ[1] : SSet.{u})) ≫ d.homotopy.h
  have hb : H ≫ p = SSet.const b := by
    rw [Category.assoc, d.homotopy_comp, ← Category.assoc, whiskerRight_fst,
      Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι_comp, SSet.comp_const]
  let L := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift p b H hb
  refine { h := L, h₀ := ?_, h₁ := ?_, rel := ?_ }
  · apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_hom_ext p b
    change (SSet.ι₀ ≫ L) ≫ ι = ι
    rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift_ι]
    change SSet.ι₀ ≫ (ι ▷ (Δ[1] : SSet.{u})) ≫ d.homotopy.h = ι
    rw [← Category.assoc, SSet.ι₀_comp, Category.assoc, d.homotopy.h₀, Category.comp_id]
  · apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_hom_ext p b
    change (SSet.ι₁ ≫ L) ≫ ι = SSet.const (d.fiberPoint b) ≫ ι
    rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift_ι]
    change SSet.ι₁ ≫ (ι ▷ (Δ[1] : SSet.{u})) ≫ d.homotopy.h =
      SSet.const (d.fiberPoint b) ≫ ι
    rw [← Category.assoc, SSet.ι₁_comp, Category.assoc, d.homotopy.h₁,
      ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι_comp, SSet.const_comp, SSet.const_comp]
    rfl
  · apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro s
    exact False.elim s.1.property

/-- 概要：底上の収縮を持つ射の Kan fiber は可縮 Kan 複体。
方針：fiber 内の実際の収縮を一点へのホモトピー retract として使う。
規約：fiber の Kan 性だけを追加仮定する。
使われ方：左右 cofinal な fibration の各 fiber の境界充填。 -/
lemma CofinalSectionHomotopy.fiber_isContractibleKan {E B : SSet.{u}} {p : E ⟶ B}
    (d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.CofinalSectionHomotopy p) (b : B _⦋0⦌) [KanComplex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p b)] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p b) := by
  let g : (⊤_ SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p b := SSet.const (d.fiberPoint b)
  apply _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.isContractibleKan_of_homotopy_retract (terminal.from (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p b)) g
  · change SSet.Homotopy (𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p b))
      (terminal.from (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p b) ≫ SSet.const (d.fiberPoint b))
    rw [SSet.comp_const]
    exact d.fiberContraction b
  · exact _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.isContractibleKan_terminal

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality
