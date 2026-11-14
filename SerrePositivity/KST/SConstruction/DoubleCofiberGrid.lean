module
public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.Subdivision.InternalUncurryEdgeEvaluation
public import SerrePositivity.KST.SConstruction.CofiberEndofunctor

/-! # 二重 cofiber 図式の下辺の格子
概要：cofiber 図式を値とする cofiber 族から、二つの下辺方向の四角形を抽出する。
方針：二回の入力射影と内部 uncurry を使い、行・列の制限を厳密に計算する。
規約：選択した cofiber へ置き換えない。使われ方：相対切断の中央評価の逆同型。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open SerrePositivity.InfinityCategories
open scoped _root_.Simplicial

/-- cofiber 四角形の下辺の指定端点での評価。 -/
def cofiberBottomEvaluationMap (C : SSet.{u}) (j : Fin 2) : cofiberDiagrams C ⟶ C :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ IsCofiberDiagramVertex).ι ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt
    (stdSimplex.obj₀Equiv.symm j, stdSimplex.obj₀Equiv.symm (0 : Fin 2))

/-- 入力射影の端点評価は元の下辺の角の評価。 -/
lemma cofiberProjection_evaluation (C : SSet.{u}) (j : Fin 2) :
    cofiberProjection C ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm j) =
      cofiberBottomEvaluationMap C j := by
  rw [cofiberProjection, Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.stable_pre_evaluateFunctorAt]
  rfl

/-- cofiber 後合成は元の入力の辺への射影と厳密に可換。 -/
lemma cofiberPostcomp_projection {C D : SSet.{u}} (f : C ⟶ D) (hf : PreservesCofiberData f) :
    cofiberPostcomp f hf ≫ cofiberProjection D =
      cofiberProjection C ≫ (ihom (Δ[1] : SSet.{u})).map f := by
  rw [cofiberProjection, ← Category.assoc, cofiberPostcomp_ι, Category.assoc,
    (pre _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge).naturality]
  rfl

/-- 二重 cofiber 族の二つの入力の辺を四角形に並べる。 -/
def doubleCofiberGrid {E C : SSet.{u}} (J : E ⟶ cofiberDiagrams (cofiberDiagrams C)) :
    E ⟶ (ihom (Δ[1] ⊗ Δ[1] : SSet.{u})).obj C :=
  J ≫ cofiberProjection (cofiberDiagrams C) ≫
    (ihom (Δ[1] : SSet.{u})).map (cofiberProjection C) ≫
      ihomUncurry (Δ[1] : SSet.{u}) (Δ[1] : SSet.{u}) C

/-- 格子の行を与える元の外側 cofiber の下辺の端点。 -/
def doubleCofiberRow {E C : SSet.{u}} (J : E ⟶ cofiberDiagrams (cofiberDiagrams C)) (j : Fin 2) :
    E ⟶ cofiberDiagrams C := J ≫ cofiberBottomEvaluationMap (cofiberDiagrams C) j

/-- 格子の列を与える元の内側 cofiber の下辺の端点への完全な後合成。 -/
def doubleCofiberColumn {E C : SSet.{u}} [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable C]
    (J : E ⟶ cofiberDiagrams (cofiberDiagrams C)) (j : Fin 2) : E ⟶ cofiberDiagrams C :=
  J ≫ cofiberPostcomp (cofiberBottomEvaluationMap C j)
    (cofiberEvaluation_preservesSConstructionData C _).toCofiberData

/-- 格子の各行の全単体は元の外側端点の cofiber 族の入力そのもの。 -/
lemma doubleCofiberGrid_row {E C : SSet.{u}}
    (J : E ⟶ cofiberDiagrams (cofiberDiagrams C)) (j : Fin 2) :
    doubleCofiberGrid J ≫ (pre (lift (𝟙 (Δ[1] : SSet.{u}))
        (SSet.const (stdSimplex.obj₀Equiv.symm j)))).app C =
      doubleCofiberRow J j ≫ cofiberProjection C := by
  simp only [doubleCofiberGrid, Category.assoc]
  rw [_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ihomUncurry_pre_row, ihom_postcomp_evaluate]
  simpa only [doubleCofiberRow, Category.assoc] using
    congrArg (fun f => J ≫ f ≫ cofiberProjection C)
      (cofiberProjection_evaluation (cofiberDiagrams C) j)

/-- 格子の各列の全単体は元の内側端点への cofiber 後合成の入力そのもの。 -/
lemma doubleCofiberGrid_column {E C : SSet.{u}} [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable C]
    (J : E ⟶ cofiberDiagrams (cofiberDiagrams C)) (j : Fin 2) :
    doubleCofiberGrid J ≫ (pre (lift (SSet.const (stdSimplex.obj₀Equiv.symm j))
        (𝟙 (Δ[1] : SSet.{u})))).app C =
      doubleCofiberColumn J j ≫ cofiberProjection C := by
  simp only [doubleCofiberGrid, Category.assoc]
  rw [_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ihomUncurry_pre_column, ← CategoryTheory.Functor.map_comp, cofiberProjection_evaluation]
  simpa only [doubleCofiberColumn, Category.assoc] using
    congrArg (fun f => J ≫ f)
      (cofiberPostcomp_projection (cofiberBottomEvaluationMap C j)
        (cofiberEvaluation_preservesSConstructionData C _).toCofiberData).symm

end SerrePositivity.KST.SConstruction
