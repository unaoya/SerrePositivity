module

public meta import SerrePositivity.InfinityCategories.Simplicial.DeprecatedAlias

public import SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierUniformTerminalRefinement

/-!
概要：元の実分母・次辺の全族から、同じ固定頂点を持つ終端側の余錐族を構成する。
方針：構成済みの終端 pullback の全境界式を回収し、実 attachment を部分族なしで適用する。
規約：余錐族や共有始域の整合を追加入力にしない。
使われ方：相対回収円柱の終端の正規化と、同じ相対 corner の境界データ。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories SerrePositivity.KST.Fibration
namespace SerrePositivity.KST.LocalizingInvariants
end SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.InfinityCategories.Derived.Verdier.Fractions
open SerrePositivity.KST.LocalizingInvariants

local instance normalizedStableFiniteLimits {X : SSet.{u}} [Quasicategory X] [IsStable X] :
    HasFiniteLimits X := hasFiniteLimits_of_isStable _

local instance normalizedStableParameterFiniteLimits {X P : SSet.{u}}
    [Quasicategory X] [IsStable X] : HasFiniteLimits ((ihom P).obj X) :=
  hasFiniteLimits_functorCategory _ _

/-- 元の実次辺族を、同じ精密化前段と固定頂点を持つ全余錐族へ貼る。 -/
lemma exists_verdierSpanCoconeFamily {A B : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.StableCategory.{u}} (i : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap A B)
    (x z : B.obj _⦋0⦌) {P : SSet.{u}} {n : ℕ}
    (g : P ⟶ _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierDenominatorSpanFamily i x z)
    (F : P ⟶ (ihom (Δ[n] : SSet.{u})).obj (pullbackDiagrams B.obj))
    (hF : F ≫ evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (Fin.last n)) =
      _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.terminalPullbackColumnFamily (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierSpanFamilyDenominatorArrow i x z g)) :
    ∃ C : P ⟶ (ihom (join (Δ[n] : SSet.{u}) Δ[0])).obj B.obj,
      C ≫ (pre (joinInl (Δ[n] : SSet.{u}) Δ[0])).app B.obj = _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.pullbackSourcePrefixFamily F ∧
      C ≫ (pre (joinMap (_root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.simplexLastPoint n) (𝟙 Δ[0]))).app B.obj =
        _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierSpanFamilyNumeratorArrow i x z g ≫ (pre (joinStdSimplexIso 0 0).hom).app B.obj ∧
      C ≫ evaluateFunctorAt ((joinInr (Δ[n] : SSet.{u}) Δ[0]).app (Opposite.op ⦋0⦌)
        (stdSimplex.obj₀Equiv.symm (0 : Fin 1))) = SSet.const z := by
  obtain ⟨C, _, hp, hn, hz⟩ := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.exists_relative_verdierSpanCoconeFamily i x z
    (initial.to P) g F hF
    (initial.to ((ihom (join (Δ[n] : SSet.{u}) Δ[0])).obj B.obj))
    (initialIsInitial.hom_ext _ _) (initialIsInitial.hom_ext _ _)
  exact ⟨C, hp, hn, hz⟩

/-- 実分母添字の同じ辺族は、元の実 span の同じ分母辺族を転置したもの。 -/
lemma verdierDenominatorFamilyEdge_span {A B : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.StableCategory.{u}} (i : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap A B)
    (x z : B.obj _⦋0⦌) {P : SSet.{u}} (a : P ⟶ _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierDenominatorSpanFamily i x z) :
    _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierDenominatorFamilyEdge i x (a ≫ _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierDenominatorSpanProjection i x z) =
      internalHomFlipHomEquiv P Δ[1] B.obj (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierSpanFamilyDenominatorArrow i x z a) := by
  simp only [_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierDenominatorFamilyEdge, _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierSpanFamilyDenominatorArrow, Category.assoc]

/-- 元の境界実 span 族から、全境界式・固定頂点・同じ次辺を持つ正規化余錐を構成する。 -/
lemma exists_verdierNormalizedSpanCoconeFamily
    {A B C : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.StableCategory.{u}} {i : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap A B} {q : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap B C}
    (h : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.IsVerdierSequence i q) {n : ℕ} (D : (Δ[n] : SSet.{u}) ⟶ B.obj)
    (z : B.obj _⦋0⦌) {P : SSet.{u}}
    (a : P ⟶ _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierDenominatorSpanFamily i
      (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))) z) :
    ∃ (R : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶
        (ihom (Δ[n] : SSet.{u})).obj ((ihom P).obj B.obj)) (hR : IsPullbackSquare R)
      (E : P ⟶ (ihom (join (Δ[n] : SSet.{u}) Δ[0])).obj B.obj),
      squareVertex R 0 1 = functorVertex (D ≫ constantFunctorMap P B.obj) ∧
      squareRightEdge ≫ R = internalHomFlipHomEquiv Δ[n] Δ[1] ((ihom P).obj B.obj)
        (SSet.const (functorVertex (internalHomFlipHomEquiv P Δ[1] B.obj
          (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierSpanFamilyDenominatorArrow i
            (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))) z a)))) ∧
      squareTopEdge ≫ R = internalHomFlipHomEquiv Δ[n] Δ[1] ((ihom P).obj B.obj)
        (_root_.SerrePositivity.InfinityCategories.Core.Quasicategory.simplexTerminalArrowFamily (D ≫ constantFunctorMap P B.obj)) ∧
      R ≫ evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (Fin.last n)) =
        squareColumnDiagram (internalHomFlipHomEquiv P Δ[1] B.obj
          (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierSpanFamilyDenominatorArrow i
            (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))) z a)) ∧
      (∀ (k : (Δ[n] : SSet.{u}) _⦋0⦌) (p : P _⦋0⦌),
        (squareLeftArrow (R ≫ evaluateFunctorAt k ≫ evaluateFunctorAt p)).edge ∈
          _root_.SerrePositivity.InfinityCategories.Stable.Verdier.Fractions.weakEquivalences i) ∧
      E ≫ (pre (joinInl (Δ[n] : SSet.{u}) Δ[0])).app B.obj =
        _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.pullbackSourcePrefixFamily (parametricPullbackDiagramFamily R hR) ∧
      E ≫ (pre (joinMap (_root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.simplexLastPoint n) (𝟙 Δ[0]))).app B.obj =
        _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierSpanFamilyNumeratorArrow i
          (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))) z a ≫
          (pre (joinStdSimplexIso 0 0).hom).app B.obj ∧
      E ≫ evaluateFunctorAt ((joinInr (Δ[n] : SSet.{u}) Δ[0]).app (Opposite.op ⦋0⦌)
        (stdSimplex.obj₀Equiv.symm (0 : Fin 1))) = SSet.const z := by
  let x := D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))
  obtain ⟨R, hR, hD, hl, _, hr, ht, hW⟩ :=
    _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.exists_verdierDenominatorFamilyTerminalRefinement h D
      (a ≫ _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierDenominatorSpanProjection i x z)
  rw [_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierDenominatorFamilyEdge_span] at hr hl
  have hF := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.parametricPullbackDiagramFamily_terminal_column R hR
    (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierSpanFamilyDenominatorArrow i x z a) hl
  obtain ⟨E, hp, hn, hz⟩ := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.exists_verdierSpanCoconeFamily i x z a
    (parametricPullbackDiagramFamily R hR) hF
  exact ⟨R, hR, E, hD, hr, ht, hl, hW, hp, hn, hz⟩

lemma verdierSpanFamilyNumeratorArrow_pre {A B : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.StableCategory.{u}} (i : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap A B)
    (x z : B.obj _⦋0⦌) {S P : SSet.{u}} (j : S ⟶ P)
    (g : P ⟶ _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierDenominatorSpanFamily i x z) :
    _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierSpanFamilyNumeratorArrow i x z (j ≫ g) =
      j ≫ _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierSpanFamilyNumeratorArrow i x z g := by
  simp only [_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierSpanFamilyNumeratorArrow, Category.assoc]

lemma verdierRecoveredBoundaryNumerator_end {A B : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.StableCategory.{u}}
    (i : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap A B) (x z : B.obj _⦋0⦌) {S : SSet.{u}}
    {a b : S ⟶ _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierDenominatorSpanFamily i x z} (L : SSet.Homotopy a b) :
    (SSet.ι₁ : S ⟶ S ⊗ (Δ[1] : SSet.{u})) ≫
      _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierSpanFamilyNumeratorArrow i x z L.h =
      _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierSpanFamilyNumeratorArrow i x z b := by
  rw [← _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierSpanFamilyNumeratorArrow_pre, L.h₁]

lemma verdierRecoveredBoundaryNumerator_start {A B : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.StableCategory.{u}}
    (i : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap A B) (x z : B.obj _⦋0⦌) {S : SSet.{u}}
    {a b : S ⟶ _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierDenominatorSpanFamily i x z} (L : SSet.Homotopy a b) :
    (SSet.ι₀ : S ⟶ S ⊗ (Δ[1] : SSet.{u})) ≫
      _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierSpanFamilyNumeratorArrow i x z L.h =
      _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierSpanFamilyNumeratorArrow i x z a := by
  rw [← _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierSpanFamilyNumeratorArrow_pre, L.h₀]

/-- 元の実回収円柱の終端から、正規化余錐と相対 corner の二脚一致を実構成する。 -/
lemma exists_verdierRecoveredEndBoundary
    {A B C : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.StableCategory.{u}} {i : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap A B} {q : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap B C}
    (h : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.IsVerdierSequence i q) {n : ℕ} (D : (Δ[n] : SSet.{u}) ⟶ B.obj)
    (z : B.obj _⦋0⦌) {S : SSet.{u}}
    (a b : S ⟶ _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierDenominatorSpanFamily i
      (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))) z)
    (L : SSet.Homotopy a b)
    (Q : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶
      (ihom (Δ[n] : SSet.{u})).obj ((ihom (S ⊗ (Δ[1] : SSet.{u}))).obj B.obj))
    (hQ : IsPullbackSquare Q)
    (hQr : squareRightEdge ≫ Q = internalHomFlipHomEquiv Δ[n] Δ[1]
      ((ihom (S ⊗ (Δ[1] : SSet.{u}))).obj B.obj)
      (SSet.const (functorVertex (internalHomFlipHomEquiv (S ⊗ (Δ[1] : SSet.{u})) Δ[1] B.obj
        (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierSpanFamilyDenominatorArrow i
          (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))) z L.h)))))
    (hQt : squareTopEdge ≫ Q = internalHomFlipHomEquiv Δ[n] Δ[1]
      ((ihom (S ⊗ (Δ[1] : SSet.{u}))).obj B.obj)
      (_root_.SerrePositivity.InfinityCategories.Core.Quasicategory.simplexTerminalArrowFamily (D ≫ constantFunctorMap (S ⊗ Δ[1]) B.obj)))
    (hQl : Q ≫ evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (Fin.last n)) =
      squareColumnDiagram (internalHomFlipHomEquiv (S ⊗ (Δ[1] : SSet.{u})) Δ[1] B.obj
        (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierSpanFamilyDenominatorArrow i
          (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))) z L.h))) :
    ∃ (R : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶
        (ihom (Δ[n] : SSet.{u})).obj ((ihom S).obj B.obj)) (hR : IsPullbackSquare R)
      (E : S ⟶ (ihom (join (Δ[n] : SSet.{u}) Δ[0])).obj B.obj),
      squareVertex R 0 1 = functorVertex (D ≫ constantFunctorMap S B.obj) ∧
      (∀ (k : (Δ[n] : SSet.{u}) _⦋0⦌) (p : S _⦋0⦌),
        (squareLeftArrow (R ≫ evaluateFunctorAt k ≫ evaluateFunctorAt p)).edge ∈
          _root_.SerrePositivity.InfinityCategories.Stable.Verdier.Fractions.weakEquivalences i) ∧
      (parametricPullbackDiagramFamily R hR ≫
          (ihom (Δ[n] : SSet.{u})).map (pullbackProjection B.obj) =
        (SSet.ι₁ : S ⟶ S ⊗ (Δ[1] : SSet.{u})) ≫ parametricPullbackDiagramFamily Q hQ ≫
          (ihom (Δ[n] : SSet.{u})).map (pullbackProjection B.obj)) ∧
      (parametricPullbackDiagramFamily R hR ≫
          (pre (_root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.simplexLastPoint n)).app (pullbackDiagrams B.obj) =
        (SSet.ι₁ : S ⟶ S ⊗ (Δ[1] : SSet.{u})) ≫ parametricPullbackDiagramFamily Q hQ ≫
          (pre (_root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.simplexLastPoint n)).app (pullbackDiagrams B.obj)) ∧
      E ≫ (pre (joinInl (Δ[n] : SSet.{u}) Δ[0])).app B.obj =
        _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.pullbackSourcePrefixFamily (parametricPullbackDiagramFamily R hR) ∧
      E ≫ (pre (joinMap (_root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.simplexLastPoint n) (𝟙 Δ[0]))).app B.obj =
        (SSet.ι₁ : S ⟶ S ⊗ (Δ[1] : SSet.{u})) ≫
          _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierSpanFamilyNumeratorArrow i
            (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))) z L.h ≫
            (pre (joinStdSimplexIso 0 0).hom).app B.obj ∧
      E ≫ evaluateFunctorAt ((joinInr (Δ[n] : SSet.{u}) Δ[0]).app (Opposite.op ⦋0⦌)
        (stdSimplex.obj₀Equiv.symm (0 : Fin 1))) = SSet.const z := by
  let x := D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))
  obtain ⟨R, hR, E, hD, hr, ht, hl, hW, hp, hn, hz⟩ :=
    _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.exists_verdierNormalizedSpanCoconeFamily h D z b
  have h₁ := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierRecoveredBoundaryDenominator_end i x z L
  have hr' : squareRightEdge ≫ R = internalHomFlipHomEquiv Δ[n] Δ[1] ((ihom S).obj B.obj)
      (SSet.const (functorVertex (internalHomFlipHomEquiv S Δ[1] B.obj
        ((SSet.ι₁ : S ⟶ S ⊗ (Δ[1] : SSet.{u})) ≫
          _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierSpanFamilyDenominatorArrow i x z L.h)))) := by
    rw [h₁]
    exact hr
  have hl' : R ≫ evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (Fin.last n)) =
      squareColumnDiagram (internalHomFlipHomEquiv S Δ[1] B.obj
        ((SSet.ι₁ : S ⟶ S ⊗ (Δ[1] : SSet.{u})) ≫
          _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierSpanFamilyDenominatorArrow i x z L.h)) := by
    rw [h₁]
    exact hl
  obtain ⟨hab, hac⟩ := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.terminalRefinementBoundary_projections
    (SSet.ι₁ : S ⟶ S ⊗ (Δ[1] : SSet.{u})) D
    (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierSpanFamilyDenominatorArrow i x z L.h) Q R hQ hR hQr hr' hQt ht hQl hl'
  refine ⟨R, hR, E, hD, hW, hab, hac, hp, ?_, hz⟩
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierRecoveredBoundaryNumerator_end]
  exact hn

end SerrePositivity.InfinityCategories.Derived.Verdier.Fractions

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.exists_verdierNormalizedSpanCoconeFamily := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.exists_verdierNormalizedSpanCoconeFamily

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.exists_verdierRecoveredEndBoundary := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.exists_verdierRecoveredEndBoundary

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.exists_verdierSpanCoconeFamily := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.exists_verdierSpanCoconeFamily

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.normalizedStableFiniteLimits := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.normalizedStableFiniteLimits

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.normalizedStableParameterFiniteLimits := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.normalizedStableParameterFiniteLimits

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.verdierDenominatorFamilyEdge_span := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierDenominatorFamilyEdge_span

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.verdierRecoveredBoundaryNumerator_end := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierRecoveredBoundaryNumerator_end

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.verdierRecoveredBoundaryNumerator_start := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierRecoveredBoundaryNumerator_start

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.verdierSpanFamilyNumeratorArrow_pre := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierSpanFamilyNumeratorArrow_pre
