module
public import SerrePositivity.KST.NonConnective.DGKappaSplitPerfRelations
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGNativeLabel
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosedNerveFunctorNaturality
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGEvaluationExact

/-!
概要：元の全 native 分裂四角形の各 Perf ラベルでの評価を同じ dg 作用へ戻す。
方針：K-S• の左定数単体の公開比較を用い、全パラメータ単体を保持する。
規約：注入・射影と二胞体を選び直さず、同じ実零三角形を評価する。
使われ方：各 Perf ラベルでの分裂 cofiber 性と加法性への接続。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction
namespace SerrePositivity.KST.NonConnective

private lemma curryFamily_evaluate {A B P : SSet.{u}} (H : A ⊗ P ⟶ B)
    (x : A _⦋0⦌) {n : ℕ} (p : P _⦋n⦌) :
    (curry H ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt x).app (Opposite.op ⦋n⦌) p =
      H.app (Opposite.op ⦋n⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant x n, p) := by
  change H.app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant x n, P.map (𝟙 _) p) = _
  rw [P.map_id]
  rfl

private lemma squareVertex_post {A B : SSet.{u}}
    (F : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ A) (g : A ⟶ B) (i j : Fin 2) :
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex (F ≫ g) i j =
      g.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex F i j) := rfl

variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D]
  {κ : Cardinal.{u}} (I : DGKappaConeInput R D κ)
  (X : PresentedPerfectDGObject R (DGKappaCone R D I))

/-- 元のラベル頂点の全退化は、K-S• の同じ native 定数単体と一致する。 -/
theorem dgKappaPerfLabel_constant (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (PresentedPerfectDGObject R (DGKappaCone R D I)))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex X) n =
      dgNativePointSimplex R (PresentedPerfectDGObject R (DGKappaCone R D I)) X n := by
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex X).pullback
    (SimplexCategory.const ⦋n⦌ ⦋0⦌ 0).toOrderHom = _
  rw [← dgNativePointSimplex_zero]
  exact dgNativePointSimplex_pullback R _ X _

/-- 全 native 関手族を元の Perf ラベルで評価すると、同じ全次数 dg ラベル作用に戻る。 -/
theorem dgKappaFullPerfFamilyMap_label_app {n : ℕ}
    (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex R (DGFunctor R (DGKappaCone R D I) (DGKappaCone R D I)) n) :
    (dgKappaFullPerfFamilyMap R D I ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex X)).app
        (Opposite.op ⦋n⦌) (ULift.up s) =
      s.map (presentedPerfectDGLabelAction R (DGKappaCone R D I) (DGKappaCone R D I) X) := by
  rw [dgKappaFullPerfFamilyMap, curryFamily_evaluate, dgKappaPerfLabel_constant,
    presentedPerfectDGNativeAction_app]
  exact presentedPerfectDGNativeActionSimplex_label R _ _ X s

/-- 元の閉関手族の全評価は、同じ閉ラベル関手の通常 nerve の実像に等しい。 -/
theorem dgKappaClosedPerfFamily_label :
    (dgKappaClosedFunctorNativeMap R D I ≫ dgKappaFullPerfFamilyMap R D I) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex X) =
      nerveMap (dgKappaPerfLabelFunctor R D I X) ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.closedNerveInclusion R (PresentedPerfectDGObject R (DGKappaCone R D I)) := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro s
  exact (dgKappaFullPerfFamilyMap_label_app R D I X (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.closedNerveSimplex s)).trans
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctor_closedNerveSimplex R _ _
      (presentedPerfectDGLabelAction R (DGKappaCone R D I) (DGKappaCone R D I) X) s)

/-- 元の二胞体を持つ同じ全分裂四角形を、同じ Perf ラベルで点ごとに評価する。 -/
def dgKappaSplitPerfPointwiseSquare (Z : DGKappaZeroInput R D I) :=
  dgKappaSplitPerfFamilySquare R D I Z ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex X)

/-- 同じ点ごとの全四角形は、元の閉分裂四角形の同じラベル関手像である。 -/
theorem dgKappaSplitPerfPointwiseSquare_closed (Z : DGKappaZeroInput R D I) :
    dgKappaSplitPerfPointwiseSquare R D I X Z =
      dgKappaSplitClosedSquare R D I Z ≫ nerveMap (dgKappaPerfLabelFunctor R D I X) ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.closedNerveInclusion R (PresentedPerfectDGObject R (DGKappaCone R D I)) := by
  change ((dgKappaSplitClosedSquare R D I Z ≫ dgKappaClosedFunctorNativeMap R D I) ≫
    dgKappaFullPerfFamilyMap R D I) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex X) = _
  rw [Category.assoc, Category.assoc, ← Category.assoc (dgKappaClosedFunctorNativeMap R D I),
    dgKappaClosedPerfFamily_label]

/-- 同じ点ごとの四角形の全単体は、元の閉関手四角形の dg ラベル作用そのもの。 -/
theorem dgKappaSplitPerfPointwiseSquare_app (Z : DGKappaZeroInput R D I) {n : ℕ}
    (t : ((Δ[1] : SSet.{max (u + 1) v}) ⊗ Δ[1]).obj (Opposite.op ⦋n⦌)) :
    (dgKappaSplitPerfPointwiseSquare R D I X Z).app (Opposite.op ⦋n⦌) t =
      (((dgKappaSplitFullNativeSquare R D I Z).app (Opposite.op ⦋n⦌) t).down).map
        (presentedPerfectDGLabelAction R (DGKappaCone R D I) (DGKappaCone R D I) X) :=
  dgKappaFullPerfFamilyMap_label_app R D I X _

/-- 同じ点ごとの評価は、元の零角を持つ実三角形である。 -/
def dgKappaSplitPerfPointwiseZeroTriangle (Z : DGKappaZeroInput R D I) :
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroTriangle (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (PresentedPerfectDGObject R (DGKappaCone R D I))) where
  square := dgKappaSplitPerfPointwiseSquare R D I X Z
  zero_corner := by
    dsimp only [dgKappaSplitPerfPointwiseSquare]
    rw [squareVertex_post, dgKappaSplitPerfFamilySquare_corner,
      dgKappaFullPerfFamilyMap_vertex, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt_functorVertex]
    exact dgKappaZeroPerfAction_values R D I Z (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex X)

/-- 同じ点ごとの四角形の cofiber 普遍性は、元の実 Perf 評価の後で判定できる。 -/
theorem dgKappaSplitPerfPointwiseSquare_isPushout_iff_evaluation (Z : DGKappaZeroInput R D I) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare (dgKappaSplitPerfPointwiseSquare R D I X Z) ↔
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare (dgKappaSplitPerfPointwiseSquare R D I X Z ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (presentedPerfectDGEvaluation R (DGKappaCone R D I))) := by
  let C := DGKappaCone R D I
  let L := dgKappaSplitPerfPointwiseSquare R D I X Z
  let e := presentedPerfectDGNerveEquivalence R C
  let := presentedPerfectDGNerve_isStable R C
  let : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (PerfectDGModule R C)) :=
    (perfectDGStableModel R C Set.univ).stable
  let := presentedPerfectDGEvaluationNerve_isExactFunctor R C
  constructor
  · exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor.preservesPushoutSquare _ L
  · intro h
    have hp := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable.pullback_of_pushout_square _ h
    have hl : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare L := by
      apply (e.isLimitCone_iff (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCone L)).mpr
      simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCone, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCone,
        Category.assoc, e, L, C, presentedPerfectDGNerveEquivalence_hom] using hp
    exact _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable.pushout_of_pullback_square L hl

end SerrePositivity.KST.NonConnective
