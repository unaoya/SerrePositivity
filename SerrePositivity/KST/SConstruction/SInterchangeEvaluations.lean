module
public import SerrePositivity.KST.SConstruction.SInterchangeNaturality
public import SerrePositivity.KST.SConstruction.SClosedStableIso

/-! # 二重 S 交換と元の Ar 評価の可換性
概要：交換同型は外側の Ar 評価と内側の Ar 評価への後合成を厳密に対応させる。
方針：二重内部 Hom の包含と二方向の評価の交換式を使う。
規約：全高次パラメーターで元の評価そのもの。使われ方：S₁ 比較と前段比較の照合。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 交換後の内側の Ar 評価への後合成は交換前の外側の元の評価そのもの。 -/
lemma sInterchangeStableIso_evaluate_left (m n : ℕ) (X : StableModel.{u})
    (a : (arNerve m) _⦋0⦌) :
    (sInterchangeStableIso m n X).hom ≫ (sEndofunctor n).map (sStableEvaluation m X a) =
      sStableEvaluation m (sStableModel n X) a := by
  have hp : ((sEndofunctor n).map (sStableEvaluation m X a)).val ≫
      (gappedSubcomplex n X.carrier).ι = sDoubleInclusion n m X.carrier ≫
    (ihom (arNerve n)).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := X.carrier) a) := by
    calc
      _ = (gappedSubcomplex n (sConstruction m X.carrier)).ι ≫
          (ihom (arNerve n)).map
            ((gappedSubcomplex m X.carrier).ι ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt a) :=
        sPostcompCofiber_ι n (sStableEvaluation m X a).val (sStableEvaluation m X a).property
      _ = _ := by rw [CategoryTheory.Functor.map_comp, ← Category.assoc]; rfl
  have hr : (sStableEvaluation m (sStableModel n X) a).val ≫
      (gappedSubcomplex n X.carrier).ι = sDoubleInclusion m n X.carrier ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := (ihom (arNerve n)).obj X.carrier) a := by
    change ((gappedSubcomplex m (sConstruction n X.carrier)).ι ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt a) ≫
      (gappedSubcomplex n X.carrier).ι =
      ((gappedSubcomplex m (sConstruction n X.carrier)).ι ≫
        (ihom (arNerve m)).map (gappedSubcomplex n X.carrier).ι) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt a
    simp only [Category.assoc, ihom_postcomp_evaluate]
  apply Subtype.ext
  change sInterchange m n X.carrier ≫ ((sEndofunctor n).map (sStableEvaluation m X a)).val = _
  apply (cancel_mono (gappedSubcomplex n X.carrier).ι).mp
  rw [Category.assoc, hp, ← Category.assoc, sInterchange_doubleInclusion,
    Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.internalHomSwapIso_evaluate]
  exact hr.symm

/-- 交換後の外側の元の Ar 評価は交換前の内側の評価への後合成そのもの。 -/
lemma sInterchangeStableIso_evaluate_right (m n : ℕ) (X : StableModel.{u})
    (b : (arNerve n) _⦋0⦌) :
    (sInterchangeStableIso m n X).hom ≫ sStableEvaluation n (sStableModel m X) b =
      (sEndofunctor m).map (sStableEvaluation n X b) := by
  have hi : (sInterchangeStableIso m n X).hom ≫ (sInterchangeStableIso n m X).hom = 𝟙 _ :=
    Subtype.ext (sInterchange_twice m n X.carrier)
  rw [← sInterchangeStableIso_evaluate_left n m X b, ← Category.assoc, hi, Category.id_comp]

/-- 元の S₁ 比較は唯一の非対角の Ar[1] 成分への評価に厳密に一致する。 -/
lemma sOneComparison_eq_evaluation (C : SSet.{u}) :
    sOneComparison C = (gappedSubcomplex 1 C).ι ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := C) (ComposableArrows.mk₀ (arObj (0 : Fin 2) 1 (by decide))) := by
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro F
  rfl

/-- 二重 S の交換は元の S₁ 比較を内側と外側で厳密に照合する。 -/
lemma sInterchangeStableIso_sOneComparison (n : ℕ) (X : StableModel.{u}) :
    (sInterchangeStableIso 1 n X).hom ≫ (sEndofunctor n).map (stableSOneComparison X) =
      stableSOneComparison (sStableModel n X) := by
  have he (Y : StableModel.{u}) : stableSOneComparison Y =
      sStableEvaluation 1 Y (ComposableArrows.mk₀ (arObj (0 : Fin 2) 1 (by decide))) :=
    Subtype.ext (sOneComparison_eq_evaluation Y.carrier)
  rw [he, he]
  exact sInterchangeStableIso_evaluate_left 1 n X _

end SerrePositivity.KST.SConstruction
