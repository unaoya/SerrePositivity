module

public meta import SerrePositivity.InfinityCategories.Simplicial.DeprecatedAlias

public import SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierRelativeCoconeAttachment

/-!
概要：同じ元の cospan を補完した前段族の、パラメータ境界における二脚を照合する。
方針：構成済みの全右辺・全上辺と転置の自然性を使い、終端列も元の実辺へ戻す。
規約：相対 corner の二脚一致を新たな整合仮定にせず、元の補完の公開等式から証明する。
使われ方：回収円柱の両端の既存 pullback 族を相対充填へ代入する。
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
end SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.InfinityCategories.Derived.Verdier.Fractions
open SerrePositivity.KST.LocalizingInvariants

local instance boundaryStableFiniteLimits {X : SSet.{u}} [Quasicategory X] [IsStable X] :
    HasFiniteLimits X := hasFiniteLimits_of_isStable _

local instance boundaryStableParameterFiniteLimits {X P : SSet.{u}}
    [Quasicategory X] [IsStable X] : HasFiniteLimits ((ihom P).obj X) :=
  hasFiniteLimits_functorCategory _ _

/-- 元の終端辺全族は標的の後合成と厳密に可換する。 -/
lemma simplexTerminalArrowFamily_post {X Y : SSet.{u}} {n : ℕ}
    (D : (Δ[n] : SSet.{u}) ⟶ X) (f : X ⟶ Y) :
    simplexTerminalArrowFamily (D ≫ f) = simplexTerminalArrowFamily D ≫ (ihom Δ[1]).map f := by
  apply uncurry_injective
  simp only [_root_.SerrePositivity.InfinityCategories.Core.Quasicategory.simplexTerminalArrowFamily, uncurry_natural_right, uncurry_curry, Category.assoc]

/-- 指定実辺を全前段に並べた同じ右辺の、パラメータ制限の公式。 -/
lemma terminalRefinementRight_pre_parameter {P P' X : SSet.{u}} (j : P' ⟶ P)
    (n : ℕ) (s : P ⟶ (ihom (Δ[1] : SSet.{u})).obj X) :
    internalHomFlipHomEquiv Δ[n] Δ[1] ((ihom P).obj X)
        (SSet.const (functorVertex (internalHomFlipHomEquiv P Δ[1] X s))) ≫
      (ihom (Δ[n] : SSet.{u})).map ((pre j).app X) =
    internalHomFlipHomEquiv Δ[n] Δ[1] ((ihom P').obj X)
      (SSet.const (functorVertex (internalHomFlipHomEquiv P' Δ[1] X (j ≫ s)))) := by
  rw [← spanInternalHomFlip_post ((pre j).app X), SSet.const_comp,
    internalHomFlipHomEquiv_pre j s]
  rfl

/-- 元の定値前段からの全終端辺である上辺も、パラメータ制限を厳密に保持する。 -/
lemma terminalRefinementTop_pre_parameter {P P' X : SSet.{u}} {n : ℕ}
    (j : P' ⟶ P) (D : (Δ[n] : SSet.{u}) ⟶ X) :
    internalHomFlipHomEquiv Δ[n] Δ[1] ((ihom P).obj X)
        (simplexTerminalArrowFamily (D ≫ constantFunctorMap P X)) ≫
      (ihom (Δ[n] : SSet.{u})).map ((pre j).app X) =
    internalHomFlipHomEquiv Δ[n] Δ[1] ((ihom P').obj X)
      (simplexTerminalArrowFamily (D ≫ constantFunctorMap P' X)) := by
  rw [← spanInternalHomFlip_post ((pre j).app X),
    ← simplexTerminalArrowFamily_post, Category.assoc, constantFunctorMap_precomp]

/-- 同じ実辺の列四角形は、元のパラメータ制限後も同じ全列四角形。 -/
lemma terminalPullbackColumnFamily_pre_parameter {P P' X : SSet.{u}}
    [Quasicategory X] [IsStable X] (j : P' ⟶ P)
    (s : P ⟶ (ihom (Δ[1] : SSet.{u})).obj X) :
    j ≫ terminalPullbackColumnFamily s = terminalPullbackColumnFamily (j ≫ s) := by
  apply (cancel_mono (fullSubcomplexOnVertices
    ((ihom ((Δ[1] : SSet.{u}) ⊗ Δ[1])).obj X) IsPullbackDiagramVertex).ι).mp
  rw [Category.assoc, terminalPullbackColumnFamily_ι, terminalPullbackColumnFamily_ι,
    Category.assoc]

/-- 終端点での全族一致を、終端の一点図式への厳密制限一致へ戻す。 -/
lemma terminalPullbackFamily_restriction_of_evaluate {P X : SSet.{u}} {n : ℕ}
    (F G : P ⟶ (ihom (Δ[n] : SSet.{u})).obj (pullbackDiagrams X))
    (h : F ≫ evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (Fin.last n)) =
      G ≫ evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (Fin.last n))) :
    F ≫ (pre (simplexLastPoint n)).app (pullbackDiagrams X) =
      G ≫ (pre (simplexLastPoint n)).app (pullbackDiagrams X) := by
  apply (cancel_mono (pointFunctorEvaluationIso (pullbackDiagrams X)).hom).mp
  change (F ≫ (pre (simplexLastPoint n)).app (pullbackDiagrams X)) ≫
      evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 1)) =
    (G ≫ (pre (simplexLastPoint n)).app (pullbackDiagrams X)) ≫
      evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 1))
  rw [Category.assoc, Category.assoc, stable_pre_evaluateFunctorAt]
  have hp : (simplexLastPoint n).app (Opposite.op ⦋0⦌)
      (stdSimplex.obj₀Equiv.symm (0 : Fin 1)) = stdSimplex.obj₀Equiv.symm (Fin.last n) := by
    have h₀ : stdSimplex.obj₀Equiv.symm (0 : Fin 1) =
        SSet.yonedaEquiv (𝟙 (Δ[0] : SSet.{u})) := by decide
    rw [h₀, ← SSet.yonedaEquiv_comp, Category.id_comp]
    exact Equiv.apply_symm_apply _ _
  rwa [hp]

/-- 元の公開全右辺・全上辺・終端列から、境界の同じ相対 corner の二脚一致を証明する。 -/
lemma terminalRefinementBoundary_projections
    {P P' X : SSet.{u}} [Quasicategory X] [IsStable X] {n : ℕ}
    (j : P' ⟶ P) (D : (Δ[n] : SSet.{u}) ⟶ X)
    (s : P ⟶ (ihom (Δ[1] : SSet.{u})).obj X)
    (Q : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ (ihom (Δ[n] : SSet.{u})).obj ((ihom P).obj X))
    (R : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ (ihom (Δ[n] : SSet.{u})).obj ((ihom P').obj X))
    (hQ : IsPullbackSquare Q) (hR : IsPullbackSquare R)
    (hQr : squareRightEdge ≫ Q = internalHomFlipHomEquiv Δ[n] Δ[1] ((ihom P).obj X)
      (SSet.const (functorVertex (internalHomFlipHomEquiv P Δ[1] X s))))
    (hRr : squareRightEdge ≫ R = internalHomFlipHomEquiv Δ[n] Δ[1] ((ihom P').obj X)
      (SSet.const (functorVertex (internalHomFlipHomEquiv P' Δ[1] X (j ≫ s)))))
    (hQt : squareTopEdge ≫ Q = internalHomFlipHomEquiv Δ[n] Δ[1] ((ihom P).obj X)
      (simplexTerminalArrowFamily (D ≫ constantFunctorMap P X)))
    (hRt : squareTopEdge ≫ R = internalHomFlipHomEquiv Δ[n] Δ[1] ((ihom P').obj X)
      (simplexTerminalArrowFamily (D ≫ constantFunctorMap P' X)))
    (hQl : Q ≫ evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (Fin.last n)) =
      squareColumnDiagram (internalHomFlipHomEquiv P Δ[1] X s))
    (hRl : R ≫ evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (Fin.last n)) =
      squareColumnDiagram (internalHomFlipHomEquiv P' Δ[1] X (j ≫ s))) :
    (parametricPullbackDiagramFamily R hR ≫ (ihom (Δ[n] : SSet.{u})).map (pullbackProjection X) =
      j ≫ parametricPullbackDiagramFamily Q hQ ≫
        (ihom (Δ[n] : SSet.{u})).map (pullbackProjection X)) ∧
    (parametricPullbackDiagramFamily R hR ≫ (pre (simplexLastPoint n)).app (pullbackDiagrams X) =
      j ≫ parametricPullbackDiagramFamily Q hQ ≫
        (pre (simplexLastPoint n)).app (pullbackDiagrams X)) := by
  let Q' := Q ≫ (ihom (Δ[n] : SSet.{u})).map ((pre j).app X)
  have hQ' : IsPullbackSquare Q' := parametricPullbackSquare_pre_parameter j Q hQ
  have hr : squareRightEdge ≫ Q' = squareRightEdge ≫ R := by
    dsimp only [Q']
    rw [← Category.assoc, hQr, terminalRefinementRight_pre_parameter, hRr]
  have ht : squareTopEdge ≫ Q' = squareTopEdge ≫ R := by
    dsimp only [Q']
    rw [← Category.assoc, hQt, terminalRefinementTop_pre_parameter, hRt]
  constructor
  · have he := parametricPullbackDiagramFamily_projection_eq Q' R hQ' hR hr ht
    rw [parametricPullbackDiagramFamily_pre_parameter] at he
    simpa only [Category.assoc] using he.symm
  · have he : parametricPullbackDiagramFamily R hR ≫
        evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (Fin.last n)) =
        (j ≫ parametricPullbackDiagramFamily Q hQ) ≫
          evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (Fin.last n)) := by
      rw [Category.assoc, parametricPullbackDiagramFamily_terminal_column R hR _ hRl,
        parametricPullbackDiagramFamily_terminal_column Q hQ _ hQl,
        terminalPullbackColumnFamily_pre_parameter]
    simpa only [Category.assoc] using terminalPullbackFamily_restriction_of_evaluate _ _ he

/-- 元の構成の全境界式を実適用し、二脚一致を追加入力にせず相対 pullback と余錐を貼る。 -/
lemma exists_relative_verdierCanonicalBoundaryCoconeFamily
    {A B : StableCategory.{u}} (i : ExactMap A B) (x z : B.obj _⦋0⦌)
    {S P : SSet.{u}} {n : ℕ} (j : S ⟶ P) [Mono j] (D : (Δ[n] : SSet.{u}) ⟶ B.obj)
    (g : P ⟶ verdierDenominatorSpanFamily i x z)
    (Q : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶
      (ihom (Δ[n] : SSet.{u})).obj ((ihom P).obj B.obj))
    (R : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶
      (ihom (Δ[n] : SSet.{u})).obj ((ihom S).obj B.obj))
    (hQ : IsPullbackSquare Q) (hR : IsPullbackSquare R)
    (hQr : squareRightEdge ≫ Q = internalHomFlipHomEquiv Δ[n] Δ[1] ((ihom P).obj B.obj)
      (SSet.const (functorVertex (internalHomFlipHomEquiv P Δ[1] B.obj
        (verdierSpanFamilyDenominatorArrow i x z g)))))
    (hRr : squareRightEdge ≫ R = internalHomFlipHomEquiv Δ[n] Δ[1] ((ihom S).obj B.obj)
      (SSet.const (functorVertex (internalHomFlipHomEquiv S Δ[1] B.obj
        (j ≫ verdierSpanFamilyDenominatorArrow i x z g)))))
    (hQt : squareTopEdge ≫ Q = internalHomFlipHomEquiv Δ[n] Δ[1] ((ihom P).obj B.obj)
      (simplexTerminalArrowFamily (D ≫ constantFunctorMap P B.obj)))
    (hRt : squareTopEdge ≫ R = internalHomFlipHomEquiv Δ[n] Δ[1] ((ihom S).obj B.obj)
      (simplexTerminalArrowFamily (D ≫ constantFunctorMap S B.obj)))
    (hQl : Q ≫ evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (Fin.last n)) =
      squareColumnDiagram (internalHomFlipHomEquiv P Δ[1] B.obj
        (verdierSpanFamilyDenominatorArrow i x z g)))
    (hRl : R ≫ evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (Fin.last n)) =
      squareColumnDiagram (internalHomFlipHomEquiv S Δ[1] B.obj
        (j ≫ verdierSpanFamilyDenominatorArrow i x z g)))
    (a : S ⟶ (ihom (join (Δ[n] : SSet.{u}) Δ[0])).obj B.obj)
    (ha : pullbackSourcePrefixFamily (parametricPullbackDiagramFamily R hR) =
      a ≫ (pre (joinInl (Δ[n] : SSet.{u}) Δ[0])).app B.obj)
    (hb : j ≫ (verdierSpanFamilyNumeratorArrow i x z g ≫
        (pre (joinStdSimplexIso 0 0).hom).app B.obj) =
      a ≫ (pre (joinMap (simplexLastPoint n) (𝟙 Δ[0]))).app B.obj) :
    ∃ (F : P ⟶ (ihom (Δ[n] : SSet.{u})).obj (pullbackDiagrams B.obj))
      (L : P ⟶ (ihom (join (Δ[n] : SSet.{u}) Δ[0])).obj B.obj),
      j ≫ F = parametricPullbackDiagramFamily R hR ∧
      F ≫ (ihom (Δ[n] : SSet.{u})).map (pullbackProjection B.obj) =
        parametricPullbackDiagramFamily Q hQ ≫
          (ihom (Δ[n] : SSet.{u})).map (pullbackProjection B.obj) ∧
      F ≫ (pre (simplexLastPoint n)).app (pullbackDiagrams B.obj) =
        parametricPullbackDiagramFamily Q hQ ≫
          (pre (simplexLastPoint n)).app (pullbackDiagrams B.obj) ∧
      j ≫ L = a ∧
      L ≫ (pre (joinInl (Δ[n] : SSet.{u}) Δ[0])).app B.obj = pullbackSourcePrefixFamily F ∧
      L ≫ (pre (joinMap (simplexLastPoint n) (𝟙 Δ[0]))).app B.obj =
        verdierSpanFamilyNumeratorArrow i x z g ≫
          (pre (joinStdSimplexIso 0 0).hom).app B.obj ∧
      L ≫ evaluateFunctorAt ((joinInr (Δ[n] : SSet.{u}) Δ[0]).app (Opposite.op ⦋0⦌)
        (stdSimplex.obj₀Equiv.symm (0 : Fin 1))) = SSet.const z := by
  obtain ⟨hab, hac⟩ := terminalRefinementBoundary_projections j D
    (verdierSpanFamilyDenominatorArrow i x z g) Q R hQ hR hQr hRr hQt hRt hQl hRl
  exact exists_relative_verdierSpanPullbackCoconeFamily i x z j g Q hQ hQl
    (parametricPullbackDiagramFamily R hR) hab hac a ha hb

end SerrePositivity.InfinityCategories.Derived.Verdier.Fractions

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.boundaryStableFiniteLimits := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.boundaryStableFiniteLimits

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.boundaryStableParameterFiniteLimits := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.boundaryStableParameterFiniteLimits

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.exists_relative_verdierCanonicalBoundaryCoconeFamily := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.exists_relative_verdierCanonicalBoundaryCoconeFamily

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.simplexTerminalArrowFamily_post := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.simplexTerminalArrowFamily_post

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.terminalPullbackColumnFamily_pre_parameter := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.terminalPullbackColumnFamily_pre_parameter

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.terminalPullbackFamily_restriction_of_evaluate := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.terminalPullbackFamily_restriction_of_evaluate

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.terminalRefinementBoundary_projections := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.terminalRefinementBoundary_projections

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.terminalRefinementRight_pre_parameter := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.terminalRefinementRight_pre_parameter

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.terminalRefinementTop_pre_parameter := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.terminalRefinementTop_pre_parameter
