module
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.EquivalenceLiftingPullback
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.CodiscreteNerve
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.ScaffoldFiniteTotalFibers
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.InnerFibrations.InnerFiber
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ColimitCoconeFamily

/-!
概要：零終点 span の可縮性と、固定した実 span 上の零隅四角形の始対象。
方針：二辺の相対持ち上げ、全制限写像、同じ厳密 fiber の比較を接続する。
規約：安定性・余極限は仮定しない。使われ方：一般安定性判定の押し出し構成。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

/-- 零終点 span の族と同じ固定境界を保つ比較。 -/
lemma vertexFiberι_isQCatEquivalence_of_contractible_base_of_equivalenceLifting
    {E B : SSet.{u}} [Quasicategory E] [KanComplex B] (p : E ⟶ B) [InnerFibration p]
    (hp : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.EquivalenceLifting p) (hB : _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan B) (b : B _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p b) := by
  have := hp.innerFibration
  have : Quasicategory (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p b) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.InnerFibrations.innerFibration_vertexFiber_quasicategory p b
  let j : (Δ[0] : SSet.{u}) ⟶ B := SSet.const b
  have hj : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence j := (hB.isPrecompositionEquivalence_point j).isQCatEquivalence
  have hpb : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (pullback.snd j p) :=
    (hj.pullback_snd_isPrecompositionEquivalence_of_kanEquivalenceLifting p hp).isQCatEquivalence
  let e : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p b ≅ pullback j p := (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.vertexFiber_isPullback p b).flip.isoPullback
  have he : e.hom ≫ pullback.snd j p = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p b :=
    IsPullback.isoPullback_hom_snd _
  rw [← he]
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso e).isQCatEquivalence.comp hpb

/-- 零終点 span の族と同じ固定境界を保つ比較。 -/
lemma vertexFiber_hasInitial_of_contractible_base_of_equivalenceLifting
    {E B : SSet.{u}} [Quasicategory E] [KanComplex B] (p : E ⟶ B)
    (hp : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.EquivalenceLifting p) (hB : _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan B) (b : B _⦋0⦌)
    (hi : ∃ v : E _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsInitialVertex v) :
    ∃ v : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p b) _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsInitialVertex v := by
  have := hp.innerFibration
  have : Quasicategory (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p b) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.InnerFibrations.innerFibration_vertexFiber_quasicategory p b
  let e := (vertexFiberι_isQCatEquivalence_of_contractible_base_of_equivalenceLifting
    p hp hB b).choose
  obtain ⟨v, hv⟩ := hi
  exact ⟨e.inv.app (Opposite.op ⦋0⦌) v, e.symm.map_isInitialVertex hv⟩
end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
