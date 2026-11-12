module
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.LimitProjectionExistence
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ColimitCoconeFamily
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.PullbackRightComposition
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.VertexFiberMapLifting

/-!
概要：任意の図式族で普遍錐の選択を忘れる射影と、固定頂点での始対象性の移送。
方針：全極限錐の射影を二段の引き戻しと厳密 fiber に沿って移す。
規約：安定性・余極限は仮定しない。使われ方：一般安定性判定の零隅四角形比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

/-- 図式の族と、その同じ図式上の普遍錐の選択。 -/
def universalConesOver {A K X : SSet.{u}} (p : A ⟶ (ihom K).obj X) : SSet.{u} :=
  pullback (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.limitConeProjection K X) p

/-- 入力図式を保ち、普遍錐の選択を忘れる。 -/
abbrev universalConesOverProjection {A K X : SSet.{u}} (p : A ⟶ (ihom K).obj X) :
    universalConesOver p ⟶ A := pullback.snd _ _

/-- 任意の錐に、同じ入力図式上の普遍錐の選択を加えた族。 -/
def coneChoiceObjects {A K X : SSet.{u}} (p : A ⟶ (ihom K).obj X) : SSet.{u} :=
  pullback (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coneRestriction K X) (universalConesOverProjection p ≫ p)

/-- 任意の錐を保ち、普遍錐の選択だけを忘れる実比較。 -/
def coneChoiceForget {A K X : SSet.{u}} (p : A ⟶ (ihom K).obj X) :
    coneChoiceObjects p ⟶ pullback (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coneRestriction K X) p :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.pullbackMapRightOfComp (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coneRestriction K X) p
    (universalConesOverProjection p ≫ p) (universalConesOverProjection p) rfl

/-- 選択を忘れる比較は元の全錐を厳密に保つ。 -/
lemma coneChoiceForget_diagram {A K X : SSet.{u}} (p : A ⟶ (ihom K).obj X) :
    coneChoiceForget p ≫ pullback.fst (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coneRestriction K X) p =
      pullback.fst (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coneRestriction K X) (universalConesOverProjection p ≫ p) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.pullbackMapRightOfComp_fst _ _ _ _ _

/-- 全入力図式の極限の存在から、選択を忘れる射影は自明 Kan fibration。 -/
lemma coneChoiceForget_trivialKanFibration {A K X : SSet.{u}} [Quasicategory X]
    (p : A ⟶ (ihom K).obj X) (h : ∀ d : K ⟶ X, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasLimit d) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (coneChoiceForget p) := by
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.limitConeProjection_trivialKanFibration h
  have : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (universalConesOverProjection p) := inferInstance
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.trivialKanFibration_pullbackMapRightOfComp _ _ _ _ rfl

/-- 同じ頂点を固定した厳密 fiber でも、選択を忘れる比較は自明 Kan fibration。 -/
lemma coneChoiceForget_apexFiber_trivialKanFibration {A K X : SSet.{u}} [Quasicategory X]
    (p : A ⟶ (ihom K).obj X) (h : ∀ d : K ⟶ X, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasLimit d) (x : X _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap
      (pullback.fst (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coneRestriction K X) (universalConesOverProjection p ≫ p) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.coneApexEvaluation K X)
      (pullback.fst (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coneRestriction K X) p ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.coneApexEvaluation K X)
      (coneChoiceForget p)
      (by rw [← Category.assoc, coneChoiceForget_diagram]) x) := by
  have := coneChoiceForget_trivialKanFibration p h
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.vertexFiberMap_trivialKanFibration _ _ _ _ _
end SerrePositivity.InfinityCategories.HA.StableInfinityCategories

namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories
/-- 固定頂点で普遍錐の選択を忘れ、同じ任意錐の族へ始対象性を移す。 -/
lemma coneChoiceForget_apexFiber_hasInitial {A K X : SSet.{u}} [Quasicategory X]
    (p : A ⟶ (ihom K).obj X) (h : ∀ d : K ⟶ X, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasLimit d) (x : X _⦋0⦌)
    [Quasicategory (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber
      (pullback.fst (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coneRestriction K X) p ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.coneApexEvaluation K X) x)]
    (hi : ∃ v : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber
      (pullback.fst (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coneRestriction K X) (universalConesOverProjection p ≫ p) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.coneApexEvaluation K X) x) _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsInitialVertex v) :
    ∃ v : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber
      (pullback.fst (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coneRestriction K X) p ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.coneApexEvaluation K X) x) _⦋0⦌,
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsInitialVertex v := by
  let f := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap
    (pullback.fst (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coneRestriction K X) (universalConesOverProjection p ≫ p) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.coneApexEvaluation K X)
    (pullback.fst (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coneRestriction K X) p ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.coneApexEvaluation K X)
    (coneChoiceForget p) (by rw [← Category.assoc, coneChoiceForget_diagram]) x
  have : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration f := coneChoiceForget_apexFiber_trivialKanFibration p h x
  have := quasicategory_of_innerFibration f
  let e := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.isQCatEquivalence_of_trivialKanFibration f).choose
  obtain ⟨v, hv⟩ := hi
  exact ⟨f.app (Opposite.op ⦋0⦌) v, (e.isInitialVertex_iff v).mp hv⟩
end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
