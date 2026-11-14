module

public import SerrePositivity.KST.LocalizingInvariants.VerdierSimplexDenominators
public import SerrePositivity.KST.LocalizingInvariants.PullbackDiagramFamilies
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.EquivalencePathReplacement

/-!
概要：元の標準単体図式の分母 cospan に、全境界を保つ普遍 Ore 補完を構成する。
方針：関手圏の有限極限から全 pullback 射影の自明性を実証し、同じ分母部分圏へ戻す。
規約：全パラメータ族を扱うが、商射の局所化普遍性・可逆性はまだ結論しない。
使われ方：K-6 c5 の有限図式上の相対共通精密化。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.Fibration
namespace SerrePositivity.KST.LocalizingInvariants

variable {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) (n : ℕ)

/-- 標準単体図式の pullback 射影は、全パラメータの境界を持ち上げる。
関手圏の安定性を新たに仮定せず、元の B の有限極限だけを使う。 -/
instance simplexPullbackProjection_trivialKanFibration :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (pullbackProjection ((ihom (Δ[n] : SSet.{u})).obj B.obj)) := by
  have : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasFiniteLimits B.obj := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.hasFiniteLimits_of_isStable B.obj
  have : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasFiniteLimits ((ihom (Δ[n] : SSet.{u})).obj B.obj) :=
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.hasFiniteLimits_functorCategory _ _
  have : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.limitConeProjection (horn 2 2 : SSet.{u})
      ((ihom (Δ[n] : SSet.{u})).obj B.obj)) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.limitConeProjection_trivialKanFibration (fun p => _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasFiniteLimits.hasLimit p)
  rw [← pullbackDiagramsConesIso_projection]
  exact ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.trivialKanFibrations.comp_mem _ _ (MorphismProperty.rlp_of_isIso _ _)
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration.mem⟩

/-- cospan の右辺が元の strict core 逆像に属するという、同じ全図式の条件。 -/
def IsSimplexDenominatorCospan
    (v : ((ihom (horn 2 2 : SSet.{u})).obj
      ((ihom (Δ[n] : SSet.{u})).obj B.obj)) _⦋0⦌) : Prop :=
  SSet.yonedaEquiv (horn₂₂.ι₀₂ ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv _ _).symm v) ∈
    (relativeFirstRowSimplex q n).obj (Opposite.op ⦋1⦌)

/-- 元の分母を右辺に持つ全 cospan の充満部分圏。 -/
def simplexDenominatorCospans : SSet.{u} :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ (IsSimplexDenominatorCospan q n) : SSet.{u})

/-- 全 cospan 圏への元の包含。 -/
def simplexDenominatorCospanInclusion : simplexDenominatorCospans q n ⟶
    (ihom (horn 2 2 : SSet.{u})).obj ((ihom (Δ[n] : SSet.{u})).obj B.obj) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ (IsSimplexDenominatorCospan q n)).ι

/-- 同じ分母 cospan を持つ実普遍四角形の全空間。 -/
def simplexOreDiagrams : SSet.{u} :=
  pullback (pullbackProjection ((ihom (Δ[n] : SSet.{u})).obj B.obj))
    (simplexDenominatorCospanInclusion q n)

/-- 普遍四角形から元の分母 cospan を回収する指定射影。 -/
def simplexOreProjection : simplexOreDiagrams q n ⟶ simplexDenominatorCospans q n :=
  pullback.snd _ _

/-- 元の分母 cospan 上の射影の全単射 RLP を、実基底変更から証明する。 -/
instance simplexOreProjection_trivialKanFibration :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (simplexOreProjection q n) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.trivialKanFibration_pullback_snd _ _

/-- 任意の指定部分族を保ち、元の全有限図式の Ore 補完を同じ底上で延長する。 -/
lemma exists_relative_simplexOreFamily {S T : SSet.{u}} (j : S ⟶ T) [Mono j]
    (d : T ⟶ simplexDenominatorCospans q n) (a : S ⟶ simplexOreDiagrams q n)
    (ha : a ≫ simplexOreProjection q n = j ≫ d) :
    ∃ F : T ⟶ simplexOreDiagrams q n,
      j ≫ F = a ∧ F ≫ simplexOreProjection q n = d := by
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration.mem (p := simplexOreProjection q n) j inferInstance
  have sq : CommSq a j (simplexOreProjection q n) d := ⟨ha⟩
  exact ⟨sq.lift, sq.fac_left, sq.fac_right⟩

/-- 同じ全パラメータの分母 cospan に対する、全普遍補完の選択空間。 -/
def simplexOreFamilySpace {T : SSet.{u}} (d : T ⟶ simplexDenominatorCospans q n) :
    SSet.{u} :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber ((ihom T).map (simplexOreProjection q n)) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex d)

/-- 選択空間の可縮性は、元の射影の全境界充填から実証する。 -/
lemma simplexOreFamilySpace_isContractibleKan {T : SSet.{u}}
    (d : T ⟶ simplexDenominatorCospans q n) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan (simplexOreFamilySpace q n d) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_isContractibleKan ((ihom T).map (simplexOreProjection q n)) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex d)

/-- 追加した普遍四角形の同じ全図式を頂点で読む。 -/
def simplexOreSquare (v : (simplexOreDiagrams q n) _⦋0⦌) :
    (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ (ihom (Δ[n] : SSet.{u})).obj B.obj :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv _ _).symm
    ((pullback.fst (pullbackProjection ((ihom (Δ[n] : SSet.{u})).obj B.obj))
      (simplexDenominatorCospanInclusion q n)).app (Opposite.op ⦋0⦌) v).val

/-- 記憶した四角形は、同じ有限図式圏における実引き戻し。 -/
lemma simplexOreSquare_isPullback (v : (simplexOreDiagrams q n) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare (simplexOreSquare q n v) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices_vertex
    ((pullback.fst (pullbackProjection ((ihom (Δ[n] : SSet.{u})).obj B.obj))
      (simplexDenominatorCospanInclusion q n)).app (Opposite.op ⦋0⦌) v)

/-- 記憶した四角形は同じ元の cospan を厳密に回収する。 -/
lemma simplexOreSquare_cospan (v : (simplexOreDiagrams q n) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan (simplexOreSquare q n v) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv _ _).symm
        (((simplexOreProjection q n).app (Opposite.op ⦋0⦌) v).val) := by
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv _ _).injective
  rw [Equiv.apply_symm_apply]
  have hr : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (simplexOreSquare q n v) =
      ((pullback.fst (pullbackProjection ((ihom (Δ[n] : SSet.{u})).obj B.obj))
        (simplexDenominatorCospanInclusion q n)).app (Opposite.op ⦋0⦌) v).val :=
    Equiv.apply_symm_apply _ _
  change ((pre _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.cospanSquareBoundary).app _).app (Opposite.op ⦋0⦌)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (simplexOreSquare q n v)) = _
  rw [hr]
  exact congrArg (fun f => f.app (Opposite.op ⦋0⦌) v) (pullback.condition
    (f := pullbackProjection ((ihom (Δ[n] : SSet.{u})).obj B.obj))
    (g := simplexDenominatorCospanInclusion q n))

/-- 右辺は指定した元の core 逆像の分母。 -/
lemma simplexOreSquare_right_mem (v : (simplexOreDiagrams q n) _⦋0⦌) :
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareRightArrow (simplexOreSquare q n v)).edge ∈
      (relativeFirstRowSimplex q n).obj (Opposite.op ⦋1⦌) := by
  have hv := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices_vertex
    ((simplexOreProjection q n).app (Opposite.op ⦋0⦌) v)
  change SSet.yonedaEquiv (horn₂₂.ι₀₂ ≫ _) ∈ _ at hv
  rw [← simplexOreSquare_cospan, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan, ← Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.cospanSquareBoundary_rightEdge] at hv
  rw [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareRightArrow_edge]
  exact hv

/-- 全境界充填で得た同じ四角形の左辺も、元の strict core 逆像の分母。 -/
lemma simplexOreSquare_left_mem {A : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} {i : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B}
    (h : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence i q) (v : (simplexOreDiagrams q n) _⦋0⦌) :
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareLeftArrow (simplexOreSquare q n v)).edge ∈
      (relativeFirstRowSimplex q n).obj (Opposite.op ⦋1⦌) :=
  (relativeFirstRowSimplex_pullback_iff h n _ (simplexOreSquare_isPullback q n v)).mpr
    (simplexOreSquare_right_mem q n v)

end SerrePositivity.KST.LocalizingInvariants
