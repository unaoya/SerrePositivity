module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.BaseChangeHomSection
public import SerrePositivity.InfinityCategories.F1.Fibrations.TrivialKanFunctorIsoProjection

/-!
概要：既存の大域 Hom 自然性に使う同じ持ち上げを明示し、その射影の指定値を回収する。
方針：元の一射影の切断と元の比較作用を、同じ trivial Kan fiber の中で結ぶ。
規約：既存の比較 span と切断を保持する。
使われ方：大域自然性と局所共有頂点の三角形の同型の照合。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories

variable {C D : Type u} [Category.{u} C] [Category.{u} D] (k : D ⥤ C)
  (p q : CocartesianFibrationCategory (nerve C))

/-- 元の大域 Hom 作用を、既存の一射影の指定切断で同じ比較空間へ持ち上げる。 -/
def cocartesianBaseChangeHomNaturalityLift :
    (SSet.uliftFunctor.{u + 1, u}).obj (SimplicialCategory.sHom p q) ⟶
      cocartesianBaseChangeHomComparisonSpace k p q :=
  (SSet.uliftFunctor.{u + 1, u}).map
      ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).map p q) ≫
    cocartesianStraighteningHomInterval
      ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj p)
      ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap k)).obj q) ≫
    cocartesianBaseChangeHomSpanOneSection k p q

/-- 元の二つの持ち上げの一射影は、同じ分類 Hom 作用として厳密に一致する。 -/
lemma cocartesianBaseChangeHomNaturalityLift_projection :
    cocartesianBaseChangeHomNaturalityLift k p q ≫ cocartesianBaseChangeHomSpanOne k p q =
      cocartesianBaseChangeHomComparison k p q ≫ cocartesianBaseChangeHomSpanOne k p q := by
  rw [cocartesianBaseChangeHomComparison_one]
  simp only [cocartesianBaseChangeHomNaturalityLift, Category.assoc,
    cocartesianBaseChangeHomSpanOneSection_projection, Category.comp_id]

/-- 大域自然性の元の fiber 内比較を、同じ二つの持ち上げの同型として明示する。 -/
def cocartesianBaseChangeHomNaturalityLiftIso :
    FunctorIso (cocartesianBaseChangeHomNaturalityLift k p q)
      (cocartesianBaseChangeHomComparison k p q) := by
  have : TrivialKanFibration (cocartesianBaseChangeHomSpanOne k p q) :=
    cocartesianBaseChangeHomSpanOne_trivialKanFibration k p q
  exact functorIsoOfTrivialKanFibration (cocartesianBaseChangeHomSpanOne k p q) _ _
    (cocartesianBaseChangeHomNaturalityLift_projection k p q)

/-- 元の大域自然性の fiber 内同型は、一射影後に同じ等式の同型そのものへ戻る。 -/
lemma cocartesianBaseChangeHomNaturalityLiftIso_projection :
    (cocartesianBaseChangeHomNaturalityLiftIso k p q).postcomp
        (cocartesianBaseChangeHomSpanOne k p q) =
      eqToIso (congrArg (fun v ↦ SSet.HomotopyCategory.mk (functorVertex v))
        (cocartesianBaseChangeHomNaturalityLift_projection k p q)) := by
  have : TrivialKanFibration (cocartesianBaseChangeHomSpanOne k p q) :=
    cocartesianBaseChangeHomSpanOne_trivialKanFibration k p q
  exact functorIsoOfTrivialKanFibration_postcomp (cocartesianBaseChangeHomSpanOne k p q)
    (cocartesianBaseChangeHomNaturalityLift k p q) (cocartesianBaseChangeHomComparison k p q)
    (cocartesianBaseChangeHomNaturalityLift_projection k p q)

end SerrePositivity.InfinityCategories
