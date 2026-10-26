module

public import SerrePositivity.KST.LocalizingInvariants.RelativeTerminalPullbackFamilies
public import SerrePositivity.KST.LocalizingInvariants.VerdierParametricTerminalRefinement

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
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants

/-- 元の全正方形を、パラメータごとの全図式の実正方形族へ転置する。 -/
def parametricPullbackSquares {P L X : SSet.{u}}
    (Q : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ (ihom L).obj ((ihom P).obj X)) :
    P ⟶ (ihom L).obj ((ihom ((Δ[1] : SSet.{u}) ⊗ Δ[1])).obj X) :=
  internalHomFlipHomEquiv L P ((ihom ((Δ[1] : SSet.{u}) ⊗ Δ[1])).obj X)
    (internalHomFlipHomEquiv ((Δ[1] : SSet.{u}) ⊗ Δ[1]) L ((ihom P).obj X) Q ≫
      (internalHomSwapIso ((Δ[1] : SSet.{u}) ⊗ Δ[1]) P X).hom)

/-- 転置は同じ二つの評価で得られる元の全四角形を厳密に回収する。 -/
lemma parametricPullbackSquares_evaluate {P L X : SSet.{u}}
    (Q : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ (ihom L).obj ((ihom P).obj X))
    (p : P _⦋0⦌) (l : L _⦋0⦌) :
    (evaluateFunctorAt (Y := (ihom ((Δ[1] : SSet.{u}) ⊗ Δ[1])).obj X) l).app
      (Opposite.op ⦋0⦌) ((parametricPullbackSquares Q).app (Opposite.op ⦋0⦌) p) =
      functorVertex (Q ≫ evaluateFunctorAt l ≫ evaluateFunctorAt p) := by
  rw [parametricPullbackSquares, internalHomFlipHomEquiv_app_zero,
    evaluateFunctorAt_functorVertex]
  change (evaluateFunctorAt (Y := (ihom ((Δ[1] : SSet.{u}) ⊗ Δ[1])).obj X) p).app
      (Opposite.op ⦋0⦌)
      ((internalHomSwapIso ((Δ[1] : SSet.{u}) ⊗ Δ[1]) P X).hom.app (Opposite.op ⦋0⦌)
        ((internalHomFlipHomEquiv ((Δ[1] : SSet.{u}) ⊗ Δ[1]) L ((ihom P).obj X) Q).app
          (Opposite.op ⦋0⦌) l)) = _
  rw [internalHomFlipHomEquiv_app_zero, internalHomSwapIso_functorVertex,
    evaluateFunctorAt_functorVertex]
  change (internalHomFlipHomEquiv ((Δ[1] : SSet.{u}) ⊗ Δ[1]) P X
    (Q ≫ evaluateFunctorAt l)).app (Opposite.op ⦋0⦌) p = _
  rw [internalHomFlipHomEquiv_app_zero]
  rw [Category.assoc]

/-- 各図式頂点での制限も、元のパラメータ全体の同じ四角形族として回収する。 -/
lemma parametricPullbackSquares_evaluate_family {P L X : SSet.{u}}
    (Q : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ (ihom L).obj ((ihom P).obj X)) (l : L _⦋0⦌) :
    parametricPullbackSquares Q ≫ evaluateFunctorAt l =
      internalHomFlipHomEquiv ((Δ[1] : SSet.{u}) ⊗ Δ[1]) P X
        (Q ≫ evaluateFunctorAt l) := by
  rw [parametricPullbackSquares, spanTransposeFamily_evaluate]
  change (functorVertexEquiv P ((ihom ((Δ[1] : SSet.{u}) ⊗ Δ[1])).obj X)).symm
    ((internalHomSwapIso ((Δ[1] : SSet.{u}) ⊗ Δ[1]) P X).hom.app (Opposite.op ⦋0⦌)
      ((internalHomFlipHomEquiv ((Δ[1] : SSet.{u}) ⊗ Δ[1]) L ((ihom P).obj X) Q).app
        (Opposite.op ⦋0⦌) l)) = _
  rw [internalHomFlipHomEquiv_app_zero, internalHomSwapIso_functorVertex]
  change (functorVertexEquiv P ((ihom ((Δ[1] : SSet.{u}) ⊗ Δ[1])).obj X)).symm
    ((functorVertexEquiv P ((ihom ((Δ[1] : SSet.{u}) ⊗ Δ[1])).obj X))
      (internalHomFlipHomEquiv ((Δ[1] : SSet.{u}) ⊗ Δ[1]) P X
        (Q ≫ evaluateFunctorAt l))) = _
  rw [Equiv.symm_apply_apply]

/-- 全パラメータの実 pullback 正方形を、元の pullback 部分圏の全族として回収する。 -/
def parametricPullbackDiagramFamily {P L X : SSet.{u}} [Quasicategory X]
    [HasFiniteLimits X] [HasFiniteLimits ((ihom P).obj X)]
    (Q : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ (ihom L).obj ((ihom P).obj X))
    (hQ : IsPullbackSquare Q) : P ⟶ (ihom L).obj (pullbackDiagrams X) :=
  fullSubcomplexLift (FunctorVertexSatisfies L
    ((ihom ((Δ[1] : SSet.{u}) ⊗ Δ[1])).obj X) IsPullbackDiagramVertex)
    (parametricPullbackSquares Q) (by
      intro p l
      rw [parametricPullbackSquares_evaluate]
      change IsPullbackSquare ((functorVertexEquiv _ X).symm
        ((functorVertexEquiv _ X) (Q ≫ evaluateFunctorAt l ≫ evaluateFunctorAt p)))
      rw [Equiv.symm_apply_apply]
      have hL := (isPullbackSquare_functor_iff Q).mp hQ l
      exact (isPullbackSquare_functor_iff (Q ≫ evaluateFunctorAt l)).mp hL p) ≫
    fullSubcomplexInternalHomBackward L
      ((ihom ((Δ[1] : SSet.{u}) ⊗ Δ[1])).obj X) IsPullbackDiagramVertex

/-- 元の実四角形族は、同じ包含後の全単体写像として厳密に一致する。 -/
lemma parametricPullbackDiagramFamily_ι {P L X : SSet.{u}} [Quasicategory X]
    [HasFiniteLimits X] [HasFiniteLimits ((ihom P).obj X)]
    (Q : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ (ihom L).obj ((ihom P).obj X))
    (hQ : IsPullbackSquare Q) :
    parametricPullbackDiagramFamily Q hQ ≫
      (ihom L).map (fullSubcomplexOnVertices _ IsPullbackDiagramVertex).ι =
        parametricPullbackSquares Q := by
  rw [parametricPullbackDiagramFamily, Category.assoc,
    fullSubcomplexInternalHomBackward_ι, fullSubcomplexLift_ι]

/-- 実 pullback 部分圏への回収は全パラメータの図式頂点評価とも厳密に可換。 -/
lemma parametricPullbackDiagramFamily_evaluate_ι {P L X : SSet.{u}} [Quasicategory X]
    [HasFiniteLimits X] [HasFiniteLimits ((ihom P).obj X)]
    (Q : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ (ihom L).obj ((ihom P).obj X))
    (hQ : IsPullbackSquare Q) (l : L _⦋0⦌) :
    parametricPullbackDiagramFamily Q hQ ≫ evaluateFunctorAt l ≫
      (fullSubcomplexOnVertices _ IsPullbackDiagramVertex).ι =
      internalHomFlipHomEquiv ((Δ[1] : SSet.{u}) ⊗ Δ[1]) P X
        (Q ≫ evaluateFunctorAt l) := by
  have hn : (ihom L).map (fullSubcomplexOnVertices ((ihom ((Δ[1] : SSet.{u}) ⊗ Δ[1])).obj X)
      IsPullbackDiagramVertex).ι ≫
      evaluateFunctorAt l = evaluateFunctorAt l ≫
        (fullSubcomplexOnVertices ((ihom ((Δ[1] : SSet.{u}) ⊗ Δ[1])).obj X)
      IsPullbackDiagramVertex).ι := rfl
  rw [← hn, ← Category.assoc, parametricPullbackDiagramFamily_ι,
    parametricPullbackSquares_evaluate_family]

local instance stableFiniteLimits {X : SSet.{u}} [Quasicategory X] [IsStable X] :
    HasFiniteLimits X := hasFiniteLimits_of_isStable _

local instance stableParameterFiniteLimits {X P : SSet.{u}} [Quasicategory X] [IsStable X] :
    HasFiniteLimits ((ihom P).obj X) := hasFiniteLimits_functorCategory _ _

/-- 構成済みの同じ全 pullback 族を、指定部分族へ置換しつつ cospan と終端全列を保つ。 -/
lemma exists_relative_parametricPullbackDiagramFamily
    {S P X : SSet.{u}} [Quasicategory X] [IsStable X] {n : ℕ}
    (Q : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶
      (ihom (Δ[n] : SSet.{u})).obj ((ihom P).obj X)) (hQ : IsPullbackSquare Q)
    (j : S ⟶ P) [Mono j]
    (a : S ⟶ (ihom (Δ[n] : SSet.{u})).obj (pullbackDiagrams X))
    (hab : a ≫ (ihom (Δ[n] : SSet.{u})).map (pullbackProjection X) =
      j ≫ parametricPullbackDiagramFamily Q hQ ≫
        (ihom (Δ[n] : SSet.{u})).map (pullbackProjection X))
    (hac : a ≫ (pre (simplexLastPoint n)).app (pullbackDiagrams X) =
      j ≫ parametricPullbackDiagramFamily Q hQ ≫
        (pre (simplexLastPoint n)).app (pullbackDiagrams X)) :
    ∃ F : P ⟶ (ihom (Δ[n] : SSet.{u})).obj (pullbackDiagrams X),
      j ≫ F = a ∧
      F ≫ (ihom (Δ[n] : SSet.{u})).map (pullbackProjection X) =
        parametricPullbackDiagramFamily Q hQ ≫
          (ihom (Δ[n] : SSet.{u})).map (pullbackProjection X) ∧
      F ≫ (pre (simplexLastPoint n)).app (pullbackDiagrams X) =
        parametricPullbackDiagramFamily Q hQ ≫
          (pre (simplexLastPoint n)).app (pullbackDiagrams X) := by
  apply exists_relative_terminalPullbackFamily n j a
    (parametricPullbackDiagramFamily Q hQ ≫
      (ihom (Δ[n] : SSet.{u})).map (pullbackProjection X))
    (parametricPullbackDiagramFamily Q hQ ≫
      (pre (simplexLastPoint n)).app (pullbackDiagrams X))
    hab hac
  rw [Category.assoc, Category.assoc, ← (pre (simplexLastPoint n)).naturality]

end SerrePositivity.KST.LocalizingInvariants
