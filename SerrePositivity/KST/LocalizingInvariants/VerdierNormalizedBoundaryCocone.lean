module

public import SerrePositivity.KST.LocalizingInvariants.VerdierUniformTerminalRefinement

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
open scoped Simplicial
open SerrePositivity.InfinityCategories SerrePositivity.KST.Fibration
namespace SerrePositivity.KST.LocalizingInvariants

local instance normalizedStableFiniteLimits {X : SSet.{u}} [Quasicategory X] [IsStable X] :
    HasFiniteLimits X := hasFiniteLimits_of_isStable _

local instance normalizedStableParameterFiniteLimits {X P : SSet.{u}}
    [Quasicategory X] [IsStable X] : HasFiniteLimits ((ihom P).obj X) :=
  hasFiniteLimits_functorCategory _ _

/-- 元の実次辺族を、同じ精密化前段と固定頂点を持つ全余錐族へ貼る。 -/
lemma exists_verdierSpanCoconeFamily {A B : StableCategory.{u}} (i : ExactMap A B)
    (x z : B.obj _⦋0⦌) {P : SSet.{u}} {n : ℕ}
    (g : P ⟶ verdierDenominatorSpanFamily i x z)
    (F : P ⟶ (ihom (Δ[n] : SSet.{u})).obj (pullbackDiagrams B.obj))
    (hF : F ≫ evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (Fin.last n)) =
      terminalPullbackColumnFamily (verdierSpanFamilyDenominatorArrow i x z g)) :
    ∃ C : P ⟶ (ihom (join (Δ[n] : SSet.{u}) Δ[0])).obj B.obj,
      C ≫ (pre (joinInl (Δ[n] : SSet.{u}) Δ[0])).app B.obj = pullbackSourcePrefixFamily F ∧
      C ≫ (pre (joinMap (simplexLastPoint n) (𝟙 Δ[0]))).app B.obj =
        verdierSpanFamilyNumeratorArrow i x z g ≫ (pre (joinStdSimplexIso 0 0).hom).app B.obj ∧
      C ≫ evaluateFunctorAt ((joinInr (Δ[n] : SSet.{u}) Δ[0]).app (Opposite.op ⦋0⦌)
        (stdSimplex.obj₀Equiv.symm (0 : Fin 1))) = SSet.const z := by
  obtain ⟨C, _, hp, hn, hz⟩ := exists_relative_verdierSpanCoconeFamily i x z
    (initial.to P) g F hF
    (initial.to ((ihom (join (Δ[n] : SSet.{u}) Δ[0])).obj B.obj))
    (initialIsInitial.hom_ext _ _) (initialIsInitial.hom_ext _ _)
  exact ⟨C, hp, hn, hz⟩

/-- 実分母添字の同じ辺族は、元の実 span の同じ分母辺族を転置したもの。 -/
lemma verdierDenominatorFamilyEdge_span {A B : StableCategory.{u}} (i : ExactMap A B)
    (x z : B.obj _⦋0⦌) {P : SSet.{u}} (a : P ⟶ verdierDenominatorSpanFamily i x z) :
    verdierDenominatorFamilyEdge i x (a ≫ verdierDenominatorSpanProjection i x z) =
      internalHomFlipHomEquiv P Δ[1] B.obj (verdierSpanFamilyDenominatorArrow i x z a) := by
  simp only [verdierDenominatorFamilyEdge, verdierSpanFamilyDenominatorArrow, Category.assoc]

/-- 元の境界実 span 族から、全境界式・固定頂点・同じ次辺を持つ正規化余錐を構成する。 -/
lemma exists_verdierNormalizedSpanCoconeFamily
    {A B C : StableCategory.{u}} {i : ExactMap A B} {q : ExactMap B C}
    (h : IsVerdierSequence i q) {n : ℕ} (D : (Δ[n] : SSet.{u}) ⟶ B.obj)
    (z : B.obj _⦋0⦌) {P : SSet.{u}}
    (a : P ⟶ verdierDenominatorSpanFamily i
      (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))) z) :
    ∃ (R : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶
        (ihom (Δ[n] : SSet.{u})).obj ((ihom P).obj B.obj)) (hR : IsPullbackSquare R)
      (E : P ⟶ (ihom (join (Δ[n] : SSet.{u}) Δ[0])).obj B.obj),
      squareVertex R 0 1 = functorVertex (D ≫ constantFunctorMap P B.obj) ∧
      squareRightEdge ≫ R = internalHomFlipHomEquiv Δ[n] Δ[1] ((ihom P).obj B.obj)
        (SSet.const (functorVertex (internalHomFlipHomEquiv P Δ[1] B.obj
          (verdierSpanFamilyDenominatorArrow i
            (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))) z a)))) ∧
      squareTopEdge ≫ R = internalHomFlipHomEquiv Δ[n] Δ[1] ((ihom P).obj B.obj)
        (simplexTerminalArrowFamily (D ≫ constantFunctorMap P B.obj)) ∧
      R ≫ evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (Fin.last n)) =
        squareColumnDiagram (internalHomFlipHomEquiv P Δ[1] B.obj
          (verdierSpanFamilyDenominatorArrow i
            (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))) z a)) ∧
      (∀ (k : (Δ[n] : SSet.{u}) _⦋0⦌) (p : P _⦋0⦌),
        (squareLeftArrow (R ≫ evaluateFunctorAt k ≫ evaluateFunctorAt p)).edge ∈
          weakEquivalences i) ∧
      E ≫ (pre (joinInl (Δ[n] : SSet.{u}) Δ[0])).app B.obj =
        pullbackSourcePrefixFamily (parametricPullbackDiagramFamily R hR) ∧
      E ≫ (pre (joinMap (simplexLastPoint n) (𝟙 Δ[0]))).app B.obj =
        verdierSpanFamilyNumeratorArrow i
          (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))) z a ≫
          (pre (joinStdSimplexIso 0 0).hom).app B.obj ∧
      E ≫ evaluateFunctorAt ((joinInr (Δ[n] : SSet.{u}) Δ[0]).app (Opposite.op ⦋0⦌)
        (stdSimplex.obj₀Equiv.symm (0 : Fin 1))) = SSet.const z := by
  let x := D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))
  obtain ⟨R, hR, hD, hl, _, hr, ht, hW⟩ :=
    exists_verdierDenominatorFamilyTerminalRefinement h D
      (a ≫ verdierDenominatorSpanProjection i x z)
  rw [verdierDenominatorFamilyEdge_span] at hr hl
  have hF := parametricPullbackDiagramFamily_terminal_column R hR
    (verdierSpanFamilyDenominatorArrow i x z a) hl
  obtain ⟨E, hp, hn, hz⟩ := exists_verdierSpanCoconeFamily i x z a
    (parametricPullbackDiagramFamily R hR) hF
  exact ⟨R, hR, E, hD, hr, ht, hl, hW, hp, hn, hz⟩

lemma verdierSpanFamilyNumeratorArrow_pre {A B : StableCategory.{u}} (i : ExactMap A B)
    (x z : B.obj _⦋0⦌) {S P : SSet.{u}} (j : S ⟶ P)
    (g : P ⟶ verdierDenominatorSpanFamily i x z) :
    verdierSpanFamilyNumeratorArrow i x z (j ≫ g) =
      j ≫ verdierSpanFamilyNumeratorArrow i x z g := by
  simp only [verdierSpanFamilyNumeratorArrow, Category.assoc]

lemma verdierRecoveredBoundaryNumerator_end {A B : StableCategory.{u}}
    (i : ExactMap A B) (x z : B.obj _⦋0⦌) {S : SSet.{u}}
    {a b : S ⟶ verdierDenominatorSpanFamily i x z} (L : SSet.Homotopy a b) :
    (SSet.ι₁ : S ⟶ S ⊗ (Δ[1] : SSet.{u})) ≫
      verdierSpanFamilyNumeratorArrow i x z L.h =
      verdierSpanFamilyNumeratorArrow i x z b := by
  rw [← verdierSpanFamilyNumeratorArrow_pre, L.h₁]

lemma verdierRecoveredBoundaryNumerator_start {A B : StableCategory.{u}}
    (i : ExactMap A B) (x z : B.obj _⦋0⦌) {S : SSet.{u}}
    {a b : S ⟶ verdierDenominatorSpanFamily i x z} (L : SSet.Homotopy a b) :
    (SSet.ι₀ : S ⟶ S ⊗ (Δ[1] : SSet.{u})) ≫
      verdierSpanFamilyNumeratorArrow i x z L.h =
      verdierSpanFamilyNumeratorArrow i x z a := by
  rw [← verdierSpanFamilyNumeratorArrow_pre, L.h₀]

/-- 元の実回収円柱の終端から、正規化余錐と相対 corner の二脚一致を実構成する。 -/
lemma exists_verdierRecoveredEndBoundary
    {A B C : StableCategory.{u}} {i : ExactMap A B} {q : ExactMap B C}
    (h : IsVerdierSequence i q) {n : ℕ} (D : (Δ[n] : SSet.{u}) ⟶ B.obj)
    (z : B.obj _⦋0⦌) {S : SSet.{u}}
    (a b : S ⟶ verdierDenominatorSpanFamily i
      (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))) z)
    (L : SSet.Homotopy a b)
    (Q : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶
      (ihom (Δ[n] : SSet.{u})).obj ((ihom (S ⊗ (Δ[1] : SSet.{u}))).obj B.obj))
    (hQ : IsPullbackSquare Q)
    (hQr : squareRightEdge ≫ Q = internalHomFlipHomEquiv Δ[n] Δ[1]
      ((ihom (S ⊗ (Δ[1] : SSet.{u}))).obj B.obj)
      (SSet.const (functorVertex (internalHomFlipHomEquiv (S ⊗ (Δ[1] : SSet.{u})) Δ[1] B.obj
        (verdierSpanFamilyDenominatorArrow i
          (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))) z L.h)))))
    (hQt : squareTopEdge ≫ Q = internalHomFlipHomEquiv Δ[n] Δ[1]
      ((ihom (S ⊗ (Δ[1] : SSet.{u}))).obj B.obj)
      (simplexTerminalArrowFamily (D ≫ constantFunctorMap (S ⊗ Δ[1]) B.obj)))
    (hQl : Q ≫ evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (Fin.last n)) =
      squareColumnDiagram (internalHomFlipHomEquiv (S ⊗ (Δ[1] : SSet.{u})) Δ[1] B.obj
        (verdierSpanFamilyDenominatorArrow i
          (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))) z L.h))) :
    ∃ (R : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶
        (ihom (Δ[n] : SSet.{u})).obj ((ihom S).obj B.obj)) (hR : IsPullbackSquare R)
      (E : S ⟶ (ihom (join (Δ[n] : SSet.{u}) Δ[0])).obj B.obj),
      squareVertex R 0 1 = functorVertex (D ≫ constantFunctorMap S B.obj) ∧
      (∀ (k : (Δ[n] : SSet.{u}) _⦋0⦌) (p : S _⦋0⦌),
        (squareLeftArrow (R ≫ evaluateFunctorAt k ≫ evaluateFunctorAt p)).edge ∈
          weakEquivalences i) ∧
      (parametricPullbackDiagramFamily R hR ≫
          (ihom (Δ[n] : SSet.{u})).map (pullbackProjection B.obj) =
        (SSet.ι₁ : S ⟶ S ⊗ (Δ[1] : SSet.{u})) ≫ parametricPullbackDiagramFamily Q hQ ≫
          (ihom (Δ[n] : SSet.{u})).map (pullbackProjection B.obj)) ∧
      (parametricPullbackDiagramFamily R hR ≫
          (pre (simplexLastPoint n)).app (pullbackDiagrams B.obj) =
        (SSet.ι₁ : S ⟶ S ⊗ (Δ[1] : SSet.{u})) ≫ parametricPullbackDiagramFamily Q hQ ≫
          (pre (simplexLastPoint n)).app (pullbackDiagrams B.obj)) ∧
      E ≫ (pre (joinInl (Δ[n] : SSet.{u}) Δ[0])).app B.obj =
        pullbackSourcePrefixFamily (parametricPullbackDiagramFamily R hR) ∧
      E ≫ (pre (joinMap (simplexLastPoint n) (𝟙 Δ[0]))).app B.obj =
        (SSet.ι₁ : S ⟶ S ⊗ (Δ[1] : SSet.{u})) ≫
          verdierSpanFamilyNumeratorArrow i
            (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))) z L.h ≫
            (pre (joinStdSimplexIso 0 0).hom).app B.obj ∧
      E ≫ evaluateFunctorAt ((joinInr (Δ[n] : SSet.{u}) Δ[0]).app (Opposite.op ⦋0⦌)
        (stdSimplex.obj₀Equiv.symm (0 : Fin 1))) = SSet.const z := by
  let x := D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))
  obtain ⟨R, hR, E, hD, hr, ht, hl, hW, hp, hn, hz⟩ :=
    exists_verdierNormalizedSpanCoconeFamily h D z b
  have h₁ := verdierRecoveredBoundaryDenominator_end i x z L
  have hr' : squareRightEdge ≫ R = internalHomFlipHomEquiv Δ[n] Δ[1] ((ihom S).obj B.obj)
      (SSet.const (functorVertex (internalHomFlipHomEquiv S Δ[1] B.obj
        ((SSet.ι₁ : S ⟶ S ⊗ (Δ[1] : SSet.{u})) ≫
          verdierSpanFamilyDenominatorArrow i x z L.h)))) := by
    rw [h₁]
    exact hr
  have hl' : R ≫ evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (Fin.last n)) =
      squareColumnDiagram (internalHomFlipHomEquiv S Δ[1] B.obj
        ((SSet.ι₁ : S ⟶ S ⊗ (Δ[1] : SSet.{u})) ≫
          verdierSpanFamilyDenominatorArrow i x z L.h)) := by
    rw [h₁]
    exact hl
  obtain ⟨hab, hac⟩ := terminalRefinementBoundary_projections
    (SSet.ι₁ : S ⟶ S ⊗ (Δ[1] : SSet.{u})) D
    (verdierSpanFamilyDenominatorArrow i x z L.h) Q R hQ hR hQr hr' hQt ht hQl hl'
  refine ⟨R, hR, E, hD, hW, hab, hac, hp, ?_, hz⟩
  rw [← Category.assoc, verdierRecoveredBoundaryNumerator_end]
  exact hn

end SerrePositivity.KST.LocalizingInvariants
