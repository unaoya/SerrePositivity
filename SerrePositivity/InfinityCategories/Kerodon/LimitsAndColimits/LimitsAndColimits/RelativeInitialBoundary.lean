module

public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.BoundaryOpposite
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.Cocone
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.Equivalence
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.InitialOpposite
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.JoinBoundary
public import SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.Opposite
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.RelativeOuterHornOp
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.RelativeTerminalExtension
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.Terminal
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.VertexFiber
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.CoconeFamily
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ColimitCoconeFamily
public import Mathlib.Tactic.CrossRefAttribute

/-! # 相対始対象の境界充填

概要：射の上で最初の頂点を固定した境界を充填する条件を終点版と比較する。
方針：標準単体と境界を反転し、指定した標的の単体を保って戻す。
規約：ファイブレーション性は定義に含めない。使われ方：普遍余錐の相対充填。

対応節は Kerodon 7.1（Tag 02H1）。
-/
@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits

/-- 概要：始点 x の正次元境界を指定された標的の単体の上で充填できる条件。
方針：全ての境界の可換正方形に持ち上げを要求する。
規約：inner fibration 性や quasicategory 性は含めない。使われ方：相対始対象の判定。 -/
def InitialBoundaryLifting {X Y : SSet.{u}} (p : X ⟶ Y) (x : X _⦋0⦌) : Prop :=
  ∀ (n : ℕ) (a : (boundary (n + 1) : SSet.{u}) ⟶ X) (b : (Δ[n + 1] : SSet.{u}) ⟶ Y),
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n 0 ≫ a = SSet.yonedaEquiv.symm x →
      CommSq a (boundary (n + 1)).ι p b →
        ∃ F : (Δ[n + 1] : SSet.{u}) ⟶ X, (boundary (n + 1)).ι ≫ F = a ∧ F ≫ p = b

/-- 概要：反転した射の終点境界充填から元の射の始点境界充填が得られる。
方針：全ての境界と標的の単体を反転し、持ち上げを反転して戻す。
規約：quasicategory 性は不要。使われ方：相対終対象の定理の双対化。 -/
lemma initialBoundaryLifting_of_terminalBoundaryLifting_op {E B : SSet.{u}}
    (p : E ⟶ B) (x : E _⦋0⦌)
    (hx : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TerminalBoundaryLifting (SSet.opFunctor.map p) (SSet.opObjEquiv.symm x)) :
    InitialBoundaryLifting p x := by
  intro n a b hfirst sq
  have hlast : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n (Fin.last (n + 1)) ≫ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.reverseBoundaryMap (n + 1) a =
      SSet.yonedaEquiv.symm (SSet.opObjEquiv.symm x) := by
    rw [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.reverseBoundaryMap_vertex, Fin.rev_last, hfirst, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.reverseSimplex_vertex]
  have sq' : CommSq (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.reverseBoundaryMap (n + 1) a) (boundary (n + 1)).ι
      (SSet.opFunctor.map p) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.reverseSimplex (n + 1) b) := by
    constructor
    rw [← _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.reverseBoundaryMap_comp, sq.w, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.reverseBoundaryMap_restrict]
  obtain ⟨F, hF, hFp⟩ := hx n _ _ hlast sq'
  let G := _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.reverseSimplex (n + 1) F ≫ (SSet.opFunctorCompOpFunctorIso.app E).hom
  refine ⟨G, ?_, ?_⟩
  · apply _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.reverseBoundaryMap_injective E (n + 1)
    rw [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.reverseBoundaryMap_restrict, _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.reverseSimplex_back]
    exact hF
  · apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.reverseSimplex_injective B (n + 1)
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.reverseSimplex_comp, _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.reverseSimplex_back]
    exact hFp

/-- 概要：射の上で始点境界を充填できる頂点は、その fiber の始対象である。
方針：標的の単体を定値に取る。
規約：ファイブレーション性は不要。使われ方：相対条件から余極限性へ戻す。 -/
@[kerodon 02WV]
lemma InitialBoundaryLifting.isInitialVertex_fiber {E B : SSet.{u}}
    (p : E ⟶ B) (b : B _⦋0⦌) (x : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p b) _⦋0⦌)
    (hx : InitialBoundaryLifting p x.val) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsInitialVertex x := by
  intro n a ha
  have hfirst : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n 0 ≫ (a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p b) =
      SSet.yonedaEquiv.symm x.val := by
    rw [← Category.assoc, ha, SSet.yonedaEquiv_symm_comp]
    rfl
  have sq : CommSq (a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p b) (boundary (n + 1)).ι p (SSet.const b) := by
    constructor
    rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι_comp, SSet.comp_const, SSet.comp_const]
  obtain ⟨F, hF, hFp⟩ := hx n _ _ hfirst sq
  refine ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift p b F hFp, ?_⟩
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_hom_ext p b
  rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift_ι]
  exact hF

/-- 概要：余錐の制限射の上で始点境界を充填できる余錐は余極限錐である。
方針：固定図式上の余錐の族の始対象性へ制限する。
規約：値域は quasicategory。逆方向は別の定理を必要とする。
使われ方：相対的な普遍性から余極限性への接続。 -/
@[kerodon 02XD]
lemma isColimitCone_of_initialBoundaryLifting_coconeRestriction
    {K X : SSet.{u}} [Quasicategory X] {p : K ⟶ X} (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone p)
    (hc : InitialBoundaryLifting (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeRestriction K X) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex c.val)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c := by
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.isColimitCone_iff_isInitialVertex_coconeFamily c).2
  exact InitialBoundaryLifting.isInitialVertex_fiber (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeRestriction K X) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex p)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeFamilyVertexEquiv p c) hc

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
