module

public import SerrePositivity.KST.LocalizingInvariants.RelativeTerminalPullbackFamilies
public import SerrePositivity.KST.LocalizingInvariants.SpanFamilyTransposeNaturality
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierParametricTerminalRefinement

/-!
概要：パラメータ付き前段 pullback 正方形を、元の実 pullback 四角形の族へ厳密に戻す。
方針：二重の内部 Hom 交換と全部分複体の内部 Hom 表示を使い、相対 corner に接続する。
規約：元の正方形・各評価・終端列・指定部分族を保持する。
使われ方：実分母輸送円柱の両端の既存族を保った pullback 補完。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants

/-- 元の全正方形を、パラメータごとの全図式の実正方形族へ転置する。 -/
def parametricPullbackSquares {P L X : SSet.{u}}
    (Q : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ (ihom L).obj ((ihom P).obj X)) :
    P ⟶ (ihom L).obj ((ihom ((Δ[1] : SSet.{u}) ⊗ Δ[1])).obj X) :=
  spanDiagramFamilyTranspose Q

/-- 元の正方形の任意の頂点も、同じ全パラメータ族として回収する。 -/
lemma parametricPullbackSquares_vertex {P L X : SSet.{u}}
    (Q : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ (ihom L).obj ((ihom P).obj X))
    (v : ((Δ[1] : SSet.{u}) ⊗ Δ[1]) _⦋0⦌) :
    parametricPullbackSquares Q ≫ (ihom L).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt v) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv L P X
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv L ((ihom P).obj X)).symm (Q.app (Opposite.op ⦋0⦌) v)) := by
  rw [parametricPullbackSquares, spanDiagramFamilyTranspose,
    ← spanInternalHomFlip_post (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt v)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv ((Δ[1] : SSet.{u}) ⊗ Δ[1]) L ((ihom P).obj X) Q ≫
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.internalHomSwapIso ((Δ[1] : SSet.{u}) ⊗ Δ[1]) P X).hom),
    Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.internalHomSwapIso_evaluate, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.spanTransposeFamily_evaluate]

/-- 転置は同じ二つの評価で得られる元の全四角形を厳密に回収する。 -/
lemma parametricPullbackSquares_evaluate {P L X : SSet.{u}}
    (Q : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ (ihom L).obj ((ihom P).obj X))
    (p : P _⦋0⦌) (l : L _⦋0⦌) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := (ihom ((Δ[1] : SSet.{u}) ⊗ Δ[1])).obj X) l).app
      (Opposite.op ⦋0⦌) ((parametricPullbackSquares Q).app (Opposite.op ⦋0⦌) p) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (Q ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt l ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt p) := by
  rw [parametricPullbackSquares, spanDiagramFamilyTranspose,
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.internalHomFlipHomEquiv_app_zero,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt_functorVertex]
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := (ihom ((Δ[1] : SSet.{u}) ⊗ Δ[1])).obj X) p).app
      (Opposite.op ⦋0⦌)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.internalHomSwapIso ((Δ[1] : SSet.{u}) ⊗ Δ[1]) P X).hom.app (Opposite.op ⦋0⦌)
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv ((Δ[1] : SSet.{u}) ⊗ Δ[1]) L ((ihom P).obj X) Q).app
          (Opposite.op ⦋0⦌) l)) = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.internalHomFlipHomEquiv_app_zero, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.internalHomSwapIso_functorVertex,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt_functorVertex]
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv ((Δ[1] : SSet.{u}) ⊗ Δ[1]) P X
    (Q ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt l)).app (Opposite.op ⦋0⦌) p = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.internalHomFlipHomEquiv_app_zero]
  rw [Category.assoc]

/-- 各図式頂点での制限も、元のパラメータ全体の同じ四角形族として回収する。 -/
lemma parametricPullbackSquares_evaluate_family {P L X : SSet.{u}}
    (Q : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ (ihom L).obj ((ihom P).obj X)) (l : L _⦋0⦌) :
    parametricPullbackSquares Q ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt l =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv ((Δ[1] : SSet.{u}) ⊗ Δ[1]) P X
        (Q ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt l) := by
  rw [parametricPullbackSquares, spanDiagramFamilyTranspose, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.spanTransposeFamily_evaluate]
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv P ((ihom ((Δ[1] : SSet.{u}) ⊗ Δ[1])).obj X)).symm
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.internalHomSwapIso ((Δ[1] : SSet.{u}) ⊗ Δ[1]) P X).hom.app (Opposite.op ⦋0⦌)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv ((Δ[1] : SSet.{u}) ⊗ Δ[1]) L ((ihom P).obj X) Q).app
        (Opposite.op ⦋0⦌) l)) = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.internalHomFlipHomEquiv_app_zero, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.internalHomSwapIso_functorVertex]
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv P ((ihom ((Δ[1] : SSet.{u}) ⊗ Δ[1])).obj X)).symm
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv P ((ihom ((Δ[1] : SSet.{u}) ⊗ Δ[1])).obj X))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv ((Δ[1] : SSet.{u}) ⊗ Δ[1]) P X
        (Q ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt l))) = _
  rw [Equiv.symm_apply_apply]

/-- 全パラメータの実 pullback 正方形を、元の pullback 部分圏の全族として回収する。 -/
def parametricPullbackDiagramFamily {P L X : SSet.{u}} [Quasicategory X]
    [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasFiniteLimits X] [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasFiniteLimits ((ihom P).obj X)]
    (Q : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ (ihom L).obj ((ihom P).obj X))
    (hQ : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare Q) : P ⟶ (ihom L).obj (pullbackDiagrams X) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.FunctorVertexSatisfies L
    ((ihom ((Δ[1] : SSet.{u}) ⊗ Δ[1])).obj X) IsPullbackDiagramVertex)
    (parametricPullbackSquares Q) (by
      intro p l
      rw [parametricPullbackSquares_evaluate]
      change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv _ X).symm
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv _ X) (Q ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt l ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt p)))
      rw [Equiv.symm_apply_apply]
      have hL := (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.isPullbackSquare_functor_iff Q).mp hQ l
      exact (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.isPullbackSquare_functor_iff (Q ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt l)).mp hL p) ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fullSubcomplexInternalHomBackward L
      ((ihom ((Δ[1] : SSet.{u}) ⊗ Δ[1])).obj X) IsPullbackDiagramVertex

/-- 元の実四角形族は、同じ包含後の全単体写像として厳密に一致する。 -/
lemma parametricPullbackDiagramFamily_ι {P L X : SSet.{u}} [Quasicategory X]
    [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasFiniteLimits X] [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasFiniteLimits ((ihom P).obj X)]
    (Q : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ (ihom L).obj ((ihom P).obj X))
    (hQ : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare Q) :
    parametricPullbackDiagramFamily Q hQ ≫
      (ihom L).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ IsPullbackDiagramVertex).ι =
        parametricPullbackSquares Q := by
  rw [parametricPullbackDiagramFamily, Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fullSubcomplexInternalHomBackward_ι, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift_ι]

/-- 実 pullback 部分圏への回収は全パラメータの図式頂点評価とも厳密に可換。 -/
lemma parametricPullbackDiagramFamily_evaluate_ι {P L X : SSet.{u}} [Quasicategory X]
    [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasFiniteLimits X] [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasFiniteLimits ((ihom P).obj X)]
    (Q : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ (ihom L).obj ((ihom P).obj X))
    (hQ : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare Q) (l : L _⦋0⦌) :
    parametricPullbackDiagramFamily Q hQ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt l ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ IsPullbackDiagramVertex).ι =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv ((Δ[1] : SSet.{u}) ⊗ Δ[1]) P X
        (Q ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt l) := by
  have hn : (ihom L).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices ((ihom ((Δ[1] : SSet.{u}) ⊗ Δ[1])).obj X)
      IsPullbackDiagramVertex).ι ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt l = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt l ≫
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices ((ihom ((Δ[1] : SSet.{u}) ⊗ Δ[1])).obj X)
      IsPullbackDiagramVertex).ι := rfl
  rw [← hn, ← Category.assoc, parametricPullbackDiagramFamily_ι,
    parametricPullbackSquares_evaluate_family]

/-- 実 pullback 族の cospan は、元の同じ全正方形の cospan 制限を転置したもの。 -/
lemma parametricPullbackDiagramFamily_projection {P L X : SSet.{u}} [Quasicategory X]
    [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasFiniteLimits X] [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasFiniteLimits ((ihom P).obj X)]
    (Q : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ (ihom L).obj ((ihom P).obj X))
    (hQ : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare Q) :
    parametricPullbackDiagramFamily Q hQ ≫ (ihom L).map (pullbackProjection X) =
      spanDiagramFamilyTranspose (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.cospanSquareBoundary ≫ Q) := by
  rw [pullbackProjection, Functor.map_comp, ← Category.assoc,
    parametricPullbackDiagramFamily_ι]
  exact (spanDiagramFamilyTranspose_pre_shape _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.cospanSquareBoundary Q).symm

/-- 元の二辺が全族で一致すれば、同じ実 pullback 族の cospan 境界も全族で一致する。 -/
lemma parametricPullbackDiagramFamily_projection_eq {P L X : SSet.{u}} [Quasicategory X]
    [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasFiniteLimits X] [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasFiniteLimits ((ihom P).obj X)]
    (Q R : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ (ihom L).obj ((ihom P).obj X))
    (hQ : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare Q) (hR : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare R)
    (hright : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge ≫ Q = _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge ≫ R)
    (htop : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareTopEdge ≫ Q = _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareTopEdge ≫ R) :
    parametricPullbackDiagramFamily Q hQ ≫ (ihom L).map (pullbackProjection X) =
      parametricPullbackDiagramFamily R hR ≫ (ihom L).map (pullbackProjection X) := by
  rw [parametricPullbackDiagramFamily_projection, parametricPullbackDiagramFamily_projection]
  congr 1
  apply horn₂₂.isPushout.hom_ext
  · simpa only [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.cospanSquareBoundary_rightEdge] using hright
  · simpa only [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.cospanSquareBoundary_topEdge] using htop

/-- パラメータ制限後の同じ全正方形も、元の各評価の pullback 性を保持する。 -/
lemma parametricPullbackSquare_pre_parameter {P P' L X : SSet.{u}} [Quasicategory X]
    [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasFiniteLimits X] [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasFiniteLimits ((ihom P).obj X)]
    [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasFiniteLimits ((ihom P').obj X)] (j : P' ⟶ P)
    (Q : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ (ihom L).obj ((ihom P).obj X))
    (hQ : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare Q) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare (Q ≫ (ihom L).map ((pre j).app X)) := by
  apply (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.isPullbackSquare_functor_iff _).mpr
  intro l
  apply (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.isPullbackSquare_functor_iff _).mpr
  intro p
  have hn : (ihom L).map ((pre j).app X) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt l =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt l ≫ (pre j).app X := rfl
  simp only [Category.assoc]
  rw [← Category.assoc ((ihom L).map ((pre j).app X))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt l) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt p), hn,
    Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.stable_pre_evaluateFunctorAt]
  have hL := (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.isPullbackSquare_functor_iff Q).mp hQ l
  exact (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.isPullbackSquare_functor_iff (Q ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt l)).mp hL
    (j.app (Opposite.op ⦋0⦌) p)

/-- 実 pullback 族の回収も、元のパラメータ制限を全単体で厳密に保持する。 -/
lemma parametricPullbackDiagramFamily_pre_parameter {P P' L X : SSet.{u}} [Quasicategory X]
    [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasFiniteLimits X] [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasFiniteLimits ((ihom P).obj X)]
    [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasFiniteLimits ((ihom P').obj X)] (j : P' ⟶ P)
    (Q : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ (ihom L).obj ((ihom P).obj X))
    (hQ : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare Q) :
    parametricPullbackDiagramFamily (Q ≫ (ihom L).map ((pre j).app X))
      (parametricPullbackSquare_pre_parameter j Q hQ) =
      j ≫ parametricPullbackDiagramFamily Q hQ := by
  have : Mono ((ihom L).map
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices ((ihom ((Δ[1] : SSet.{u}) ⊗ Δ[1])).obj X)
        IsPullbackDiagramVertex).ι) := (ihom L).map_mono _
  apply (cancel_mono ((ihom L).map
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices ((ihom ((Δ[1] : SSet.{u}) ⊗ Δ[1])).obj X)
      IsPullbackDiagramVertex).ι)).mp
  rw [parametricPullbackDiagramFamily_ι, Category.assoc, parametricPullbackDiagramFamily_ι]
  exact spanDiagramFamilyTranspose_pre_parameter j Q

local instance stableFiniteLimits {X : SSet.{u}} [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasFiniteLimits X := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.hasFiniteLimits_of_isStable _

local instance stableParameterFiniteLimits {X P : SSet.{u}} [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasFiniteLimits ((ihom P).obj X) := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.hasFiniteLimits_functorCategory _ _

/-- 構成済みの同じ全 pullback 族を、指定部分族へ置換しつつ cospan と終端全列を保つ。 -/
lemma exists_relative_parametricPullbackDiagramFamily
    {S P X : SSet.{u}} [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X] {n : ℕ}
    (Q : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶
      (ihom (Δ[n] : SSet.{u})).obj ((ihom P).obj X)) (hQ : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare Q)
    (j : S ⟶ P) [Mono j]
    (a : S ⟶ (ihom (Δ[n] : SSet.{u})).obj (pullbackDiagrams X))
    (hab : a ≫ (ihom (Δ[n] : SSet.{u})).map (pullbackProjection X) =
      j ≫ parametricPullbackDiagramFamily Q hQ ≫
        (ihom (Δ[n] : SSet.{u})).map (pullbackProjection X))
    (hac : a ≫ (pre (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.simplexLastPoint n)).app (pullbackDiagrams X) =
      j ≫ parametricPullbackDiagramFamily Q hQ ≫
        (pre (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.simplexLastPoint n)).app (pullbackDiagrams X)) :
    ∃ F : P ⟶ (ihom (Δ[n] : SSet.{u})).obj (pullbackDiagrams X),
      j ≫ F = a ∧
      F ≫ (ihom (Δ[n] : SSet.{u})).map (pullbackProjection X) =
        parametricPullbackDiagramFamily Q hQ ≫
          (ihom (Δ[n] : SSet.{u})).map (pullbackProjection X) ∧
      F ≫ (pre (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.simplexLastPoint n)).app (pullbackDiagrams X) =
        parametricPullbackDiagramFamily Q hQ ≫
          (pre (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.simplexLastPoint n)).app (pullbackDiagrams X) := by
  apply exists_relative_terminalPullbackFamily n j a
    (parametricPullbackDiagramFamily Q hQ ≫
      (ihom (Δ[n] : SSet.{u})).map (pullbackProjection X))
    (parametricPullbackDiagramFamily Q hQ ≫
      (pre (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.simplexLastPoint n)).app (pullbackDiagrams X))
    hab hac
  rw [Category.assoc, Category.assoc, ← (pre (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.simplexLastPoint n)).naturality]

end SerrePositivity.KST.LocalizingInvariants
