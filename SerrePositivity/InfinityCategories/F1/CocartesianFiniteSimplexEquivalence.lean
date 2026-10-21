module

public import SerrePositivity.InfinityCategories.F1.CocartesianScaffoldSourceRestrictionEquivalence
public import SerrePositivity.InfinityCategories.F1.CocartesianScaffoldTargetRestrictionEquivalence
public import SerrePositivity.InfinityCategories.F1.CocartesianScaffoldSegalComparison
public import SerrePositivity.InfinityCategories.F1.CocartesianTwoSimplexEquivalence

/-!
概要：元の全 Hom の同じ作用と同じ分類主写像の同値を全次元の有限単体上で閉じる。
方針：最初の辺と尾部の Segal 制限で帰納し、既存の本質的全射性と F0 を適用する。
規約：元の全 cocartesian fibrations・全相対 Hom と構成済みの分類主写像を使う。
使われ方：有限セルと骨格の降下による一般の充満忠実性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories

/-- 全有限単体で、元の全相対 Hom の core の同じ分類作用は追加仮定なしに同値。 -/
lemma cocartesianStraighteningHomInterval_finite_isQCatEquivalence (n : ℕ) :
    ∀ p q : CocartesianFibrationCategory (nerve (ULift.{u} (Fin (n + 1)))),
      IsQCatEquivalence (cocartesianStraighteningHomInterval p q) := by
  induction n with
  | zero =>
    intro p q
    exact cocartesianStraighteningHomInterval_zeroSimplex_isQCatEquivalence p q
  | succ n ih =>
    intro p q
    have htail : IsQCatEquivalence
        (cocartesianLocalHomComparison (cocartesianScaffoldTailCell n (𝟭 _)) p q) :=
      (ih _ _).comp (cocartesianBaseChangeHomTransport_isQCatEquivalence _ p q)
    have hS := cocartesianScaffoldSourceRestrictionMap_id_isQCatEquivalence n p q
    have hP := cocartesianScaffoldStrictPullbackMap_isQCatEquivalence n (𝟭 _) p q htail
    have hT := cocartesianScaffoldTargetRestrictionMap_id_isQCatEquivalence n p q
    exact hT.cancel_right ((hS.comp hP).ofFunctorIso
      (cocartesianScaffoldSegalComparisonIso n (𝟭 _) p q))

/-- 任意の底の全有限次元セルで、同じ元の局所 Hom 比較は同値。 -/
lemma cocartesianLocalHomComparison_finite_isQCatEquivalence
    {C : Type u} [Category.{u} C] (n : ℕ) (k : ULift.{u} (Fin (n + 1)) ⥤ C)
    (p q : CocartesianFibrationCategory (nerve C)) :
    IsQCatEquivalence (cocartesianLocalHomComparison k p q) :=
  (cocartesianStraighteningHomInterval_finite_isQCatEquivalence n _ _).comp
    (cocartesianBaseChangeHomTransport_isQCatEquivalence k p q)

/-- 全有限単体で、同じ元の分類主写像は充満忠実。 -/
lemma cocartesianStraighteningCoherentMap_finite_isFullyFaithful (n : ℕ) :
    IsFullyFaithful (cocartesianStraighteningCoherentMap (ULift.{u} (Fin (n + 1)))) :=
  cocartesianStraighteningCoherentMap_isFullyFaithful_of_originalHomInterval _
    (cocartesianStraighteningHomInterval_finite_isQCatEquivalence n)

/-- 全有限単体で、同じ元の分類主写像は quasicategory の同値。 -/
lemma cocartesianStraighteningCoherentMap_finite_isQCatEquivalence (n : ℕ) :
    IsQCatEquivalence (cocartesianStraighteningCoherentMap (ULift.{u} (Fin (n + 1)))) :=
  isQCatEquivalence_of_isFullyFaithful_of_isEssentiallySurjective _
    (cocartesianStraighteningCoherentMap_finite_isFullyFaithful n)
    (cocartesianStraighteningCoherentMap_isEssentiallySurjective_finite n)

/-- 元の全相対 Hom と構成済みの分類主写像を保つ、全有限単体上の分類同値。 -/
def cocartesianFiniteSimplexStraighteningEquivalence (n : ℕ) :
    QCatEquivalence (CocartesianFibrationInfinity (nerve (ULift.{u} (Fin (n + 1)))))
      (CatInfinityFunctor ((SSet.uliftFunctor.{u + 1, u}).obj
        (nerve (ULift.{u} (Fin (n + 1)))))) :=
  (cocartesianStraighteningCoherentMap_finite_isQCatEquivalence n).choose

end SerrePositivity.InfinityCategories
