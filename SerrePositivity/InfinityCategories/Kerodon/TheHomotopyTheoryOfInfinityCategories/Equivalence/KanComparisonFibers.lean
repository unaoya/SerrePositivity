module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.IntervalHomBoundary
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.FibrationDerivedFiberSpan

/-!
概要：Kan 複体間の任意の射の導来 fiber の可縮性による同値判定。
方針：両端点評価を使い path 置換の終点射を fibration にし、可縮 fiber の判定を使う。
規約：元の比較射の fibration 性は仮定しない。
使われ方：Kerodon 4.5.3.24（Tag 02VM）・7.5.4.6（Tag 03BB）、γ3b の元の q_x の導来 fiber の判定。

対応節は Kerodon 4.5（Tag 01DE）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence
noncomputable section

/-- 概要：Kan 複体間の任意の射の可逆 path 置換の終点射は Kan fibration。
方針：元の始域のホーンを先に充填し、両端点を指定した path を充填して貼る。
規約：元の射 q の fibration 性は要求しない。
使われ方：導来 fiber の可縮性から元の比較射の同値性を検出する。 -/
instance kanEquivalencePathReplacementMap_fibration {E B : SSet.{u}}
    [KanComplex E] [KanComplex B] (q : E ⟶ B) :
    Fibration (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementMap q) := by
  apply (SSet.modelCategoryQuillen.fibration_iff _).mpr
  intro T U j hj
  have : HasLiftingProperty j (terminal.from E) :=
    (SSet.modelCategoryQuillen.fibration_iff _).mp inferInstance j hj
  have : HasLiftingProperty j (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.intervalHomEndpoints B) :=
    (SSet.modelCategoryQuillen.fibration_iff _).mp inferInstance j hj
  constructor
  intro a b sq
  let e := asIso (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathι B)
  have he (i : Fin 2) : e.inv ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint B i =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm i) := by
    change e.inv ≫ e.hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm i) = _
    rw [Iso.inv_hom_id_assoc]
  let sqE : CommSq (a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementProjection q) j (terminal.from E)
      (terminal.from U) := ⟨terminal.hom_ext _ _⟩
  have hc : pullback.fst (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint B 0) q ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint B 0 =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementProjection q ≫ q := pullback.condition
  let sqP : CommSq
      (a ≫ pullback.fst (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint B 0) q ≫ e.hom) j
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.intervalHomEndpoints B) (prod.lift b (sqE.lift ≫ q)) := ⟨by
    apply prod.hom_ext
    · simp only [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.intervalHomEndpoints_fst, prod.lift_fst]
      change a ≫ pullback.fst (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint B 0) q ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint B 1 = j ≫ b
      exact sq.w
    · simp only [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.intervalHomEndpoints_snd, prod.lift_snd]
      change a ≫ (pullback.fst (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint B 0) q ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint B 0) = j ≫ sqE.lift ≫ q
      rw [hc]
      exact ((Category.assoc _ _ _).symm.trans
        (congrArg (· ≫ q) sqE.fac_left.symm)).trans (Category.assoc _ _ _)⟩
  let v := sqP.lift ≫ e.inv
  have hv : v ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint B 0 = sqE.lift ≫ q := by
    rw [Category.assoc, he, ← _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.intervalHomEndpoints_snd, ← Category.assoc,
      sqP.fac_right, prod.lift_snd]
  let l := pullback.lift v sqE.lift hv
  refine ⟨⟨{ l := l, fac_left := ?_, fac_right := ?_ }⟩⟩
  · apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst]
      change j ≫ sqP.lift ≫ e.inv = a ≫ pullback.fst (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint B 0) q
      rw [← Category.assoc, sqP.fac_left]
      simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
    · rw [Category.assoc, pullback.lift_snd]
      exact sqE.fac_left
  · change l ≫ pullback.fst (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint B 0) q ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint B 1 = b
    rw [← Category.assoc, pullback.lift_fst]
    change (sqP.lift ≫ e.inv) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint B 1 = b
    rw [Category.assoc, he, ← _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.intervalHomEndpoints_fst, ← Category.assoc,
      sqP.fac_right, prod.lift_fst]

/-- 概要：Kan 複体間の任意の射の導来 fiber は Kan 複体。
方針：path 置換の終点射の Kan fibration 性を頂点 fiber へ渡す。
規約：既存の comparisonFiber の模型を変更しない。
使われ方：元の q_x の導来 fiber の可縮性の検証。 -/
instance kanComparisonFiber_kanComplex {E B : SSet.{u}}
    [KanComplex E] [KanComplex B] (q : E ⟶ B) (b : B _⦋0⦌) :
    KanComplex (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.comparisonFiber q b) := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.fibrationVertexFiber_kanComplex _ _

/-- 概要：Kan 複体間の射が同値であることは全導来 fiber の可縮性と同値。
方針：path 置換を右ファイブレーションとして判定し、その同値性を元の射へ戻す。
規約：空の始域と標的も許し、元の射の fibration 性は要求しない。
使われ方：γ3b の元の比較 q_x による可縮性の判定。 -/
lemma homotopyEquivalence_iff_comparisonFiber_isContractibleKan {E B : SSet.{u}}
    [KanComplex E] [KanComplex B] (q : E ⟶ B) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence q ↔ ∀ b : B _⦋0⦌,
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.comparisonFiber q b) := by
  constructor
  · exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.comparisonFiber_isContractibleKan_of_homotopyEquivalence q
  · intro h
    have : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementMap q) := by
      constructor
      intro T U j hj
      cases hj with
      | @intro n i hi =>
          exact (SSet.modelCategoryQuillen.fibration_iff _).mp inferInstance _
            (horn_ι_mem_J _ i)
    have : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementMap q) :=
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.rightFibration_trivialKanFibration_of_contractible_fibers _ h
    exact ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.isQCatEquivalence_iff_equivalencePathReplacementMap q).mpr
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.isQCatEquivalence_of_trivialKanFibration _)).isSimplicialHomotopyEquivalence

end
end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence
