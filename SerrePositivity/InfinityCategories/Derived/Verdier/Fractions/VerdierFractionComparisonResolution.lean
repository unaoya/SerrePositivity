module

public import SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.WeakQuotientMappingEquivalence
public import SerrePositivity.InfinityCategories.Core.FullyFaithfulEquivalence

/-!
概要：元の Verdier 分数比較に比較経路を記憶し、全境界の持ち上げを証明する。
方針：Sp 正本の充満忠実性と元の実右逆から得た同値を、可逆経路で置換する。
規約：完成された分数の全族を扱う。有限図式の商比較への貼合せ自体は別の工程。
使われ方：c5 で共有経路と指定部分族を保って全 Hom の比較を構成する入力。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories SerrePositivity.KST.Fibration
namespace SerrePositivity.KST.LocalizingInvariants
variable {A B C : StableCategory.{u}} {i : ExactMap A B} {q : ExactMap B C}
  (h : IsVerdierSequence i q) (x y : B.obj _⦋0⦌)

/-- 完成された元の固定端点分数と、その商評価から出る比較経路の全空間。 -/
def verdierFractionComparisonResolution : SSet.{u} :=
  equivalencePathReplacement
    (fractionMappingComparison q.hom (weakEquivalences i) h.inverts x y)

/-- 同じ完成された分数を回収する射影。 -/
def verdierFractionComparisonResolutionRoof : verdierFractionComparisonResolution h x y ⟶
    groupoidCompletion (fixedMarkedSpans B.obj (weakEquivalences i) x y) :=
  equivalencePathReplacementProjection _

/-- 記憶した比較経路の終点は元の商の同じ全写像空間にある。 -/
def verdierFractionComparisonResolutionMap : verdierFractionComparisonResolution h x y ⟶
    intervalMappingSpace (q.hom.app (Opposite.op ⦋0⦌) x)
      (q.hom.app (Opposite.op ⦋0⦌) y) :=
  equivalencePathReplacementMap _

/-- 分数射影の全境界充填は、比較経路を記憶する実引き戻しによる。 -/
instance verdierFractionComparisonResolutionRoof_trivialKanFibration :
    TrivialKanFibration (verdierFractionComparisonResolutionRoof h x y) :=
  equivalencePathReplacementProjection_trivialKanFibration _

/-- 元の分数比較の全写像空間の充満忠実性から、終点射影の全境界充填を得る。 -/
instance verdierFractionComparisonResolutionMap_trivialKanFibration :
    TrivialKanFibration (verdierFractionComparisonResolutionMap h x y) := by
  have hf := verdierFractionMappingComparison_isFullyFaithful h x y
  have he := (weakFractionMappingComparison_isQCatEquivalence h x y).choose.isEssentiallySurjective
  exact hf.equivalencePathReplacementMap.trivialKanFibration_of_surjective
    he.equivalencePathReplacementMap_surjective

/-- 完成された分数の評価と元の商の族を結ぶ、同じ全比較経路。 -/
def verdierFractionComparisonResolutionIso :
    FunctorIso (verdierFractionComparisonResolutionRoof h x y ≫
      fractionMappingComparison q.hom (weakEquivalences i) h.inverts x y)
      (verdierFractionComparisonResolutionMap h x y) :=
  equivalencePathReplacementFunctorIso _

/-- 指定した部分族と商側の族を固定し、比較経路付き分数の全族を延長する。 -/
lemma exists_relative_verdierFractionComparisonFamily {S T : SSet.{u}}
    (j : S ⟶ T) [Mono j]
    (a : S ⟶ verdierFractionComparisonResolution h x y)
    (b : T ⟶ intervalMappingSpace (q.hom.app (Opposite.op ⦋0⦌) x)
      (q.hom.app (Opposite.op ⦋0⦌) y))
    (ha : a ≫ verdierFractionComparisonResolutionMap h x y = j ≫ b) :
    ∃ F : T ⟶ verdierFractionComparisonResolution h x y,
      j ≫ F = a ∧ F ≫ verdierFractionComparisonResolutionMap h x y = b := by
  have := TrivialKanFibration.mem (p := verdierFractionComparisonResolutionMap h x y)
    j inferInstance
  have sq : CommSq a j (verdierFractionComparisonResolutionMap h x y) b := ⟨ha⟩
  exact ⟨sq.lift, sq.fac_left, sq.fac_right⟩

/-- 元の全商族の上の比較経路付き分数の選択空間は可縮。 -/
lemma verdierFractionComparisonFamily_isContractibleKan {T : SSet.{u}}
    (b : T ⟶ intervalMappingSpace (q.hom.app (Opposite.op ⦋0⦌) x)
      (q.hom.app (Opposite.op ⦋0⦌) y)) :
    IsContractibleKan (vertexFiber ((ihom T).map
      (verdierFractionComparisonResolutionMap h x y)) (functorVertex b)) :=
  vertexFiber_isContractibleKan _ _

end SerrePositivity.KST.LocalizingInvariants
