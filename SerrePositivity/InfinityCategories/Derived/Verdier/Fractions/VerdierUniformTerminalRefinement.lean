module

public import SerrePositivity.InfinityCategories.Stable.Quasicategory.SimplexTerminalPullbackFamily
public import SerrePositivity.KST.LocalizingInvariants.SimplexTerminalPullbackFamily
public import SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierRefinementBoundaryProjection

/-!
概要：一つの実終端分母の補完を全パラメータで定値に保ち、同じ前段を一様に回収する。
方針：元の実 pullback 族を定値関手へ写し、転置の全単体公式で元の定値族に戻す。
規約：各パラメータで別の前段を選ばない。全 cospan と終端列も厳密に保持する。
使われ方：境界回収円柱の始端を、完成族側の一つの共通実分母に接続する。
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

local instance uniformStableFiniteLimits {X : SSet.{u}} [Quasicategory X] [IsStable X] :
    HasFiniteLimits X := hasFiniteLimits_of_isStable _

local instance uniformStableParameterFiniteLimits {X P : SSet.{u}}
    [Quasicategory X] [IsStable X] : HasFiniteLimits ((ihom P).obj X) :=
  hasFiniteLimits_functorCategory _ _

/-- 一つの実 pullback 補完を、そのまま全パラメータで定値にした全正方形。 -/
def uniformTerminalRefinementSquare {X : SSet.{u}} (P : SSet.{u}) {n : ℕ}
    (F : (Δ[n] : SSet.{u}) ⟶ pullbackDiagrams X) :
    (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ (ihom (Δ[n] : SSet.{u})).obj ((ihom P).obj X) :=
  terminalRefinementSquare F ≫ (ihom (Δ[n] : SSet.{u})).map (constantFunctorMap P X)

lemma uniformTerminalRefinementSquare_isPullback {X : SSet.{u}} [Quasicategory X]
    [IsStable X] (P : SSet.{u}) {n : ℕ} (F : (Δ[n] : SSet.{u}) ⟶ pullbackDiagrams X) :
    IsPullbackSquare (uniformTerminalRefinementSquare P F) := by
  have hF := terminalRefinementSquare_isPullback (B := ⟨X, inferInstance, inferInstance⟩) F
  apply (isPullbackSquare_functor_iff _).mpr
  intro k
  apply (isPullbackSquare_functor_iff _).mpr
  intro p
  have hn : (ihom (Δ[n] : SSet.{u})).map (constantFunctorMap P X) ≫ evaluateFunctorAt k =
      evaluateFunctorAt k ≫ constantFunctorMap P X := rfl
  simp only [uniformTerminalRefinementSquare, Category.assoc]
  rw [← Category.assoc ((ihom (Δ[n] : SSet.{u})).map (constantFunctorMap P X))
    (evaluateFunctorAt k) (evaluateFunctorAt p), hn, Category.assoc,
    spanConstantFunctorMap_evaluate, Category.comp_id]
  exact (isPullbackSquare_functor_iff _).mp hF k

/-- 全パラメータの実補完は、同じ元の一つの補完の定値族として厳密に回収される。 -/
lemma uniformTerminalRefinementSquare_family {X : SSet.{u}} [Quasicategory X] [IsStable X]
    (P : SSet.{u}) {n : ℕ} (F : (Δ[n] : SSet.{u}) ⟶ pullbackDiagrams X) :
    parametricPullbackDiagramFamily (uniformTerminalRefinementSquare P F)
      (uniformTerminalRefinementSquare_isPullback P F) = SSet.const (functorVertex F) := by
  have : Mono ((ihom (Δ[n] : SSet.{u})).map
      (fullSubcomplexOnVertices ((ihom ((Δ[1] : SSet.{u}) ⊗ Δ[1])).obj X)
        IsPullbackDiagramVertex).ι) := (ihom (Δ[n] : SSet.{u})).map_mono _
  apply (cancel_mono ((ihom (Δ[n] : SSet.{u})).map
    (fullSubcomplexOnVertices ((ihom ((Δ[1] : SSet.{u}) ⊗ Δ[1])).obj X)
      IsPullbackDiagramVertex).ι)).mp
  rw [parametricPullbackDiagramFamily_ι, parametricPullbackSquares,
    uniformTerminalRefinementSquare, spanDiagramFamilyTranspose_post_constant, SSet.const_comp]
  change SSet.const (functorVertex (internalHomFlipHomEquiv (Δ[1] ⊗ Δ[1]) Δ[n] X
    (internalHomFlipHomEquiv Δ[n] (Δ[1] ⊗ Δ[1]) X
      (F ≫ (fullSubcomplexOnVertices _ IsPullbackDiagramVertex).ι)))) =
    SSet.const (functorVertex (F ≫ (fullSubcomplexOnVertices _ IsPullbackDiagramVertex).ι))
  rw [show internalHomFlipHomEquiv (Δ[1] ⊗ Δ[1]) Δ[n] X
      (internalHomFlipHomEquiv Δ[n] (Δ[1] ⊗ Δ[1]) X
        (F ≫ (fullSubcomplexOnVertices _ IsPullbackDiagramVertex).ι)) =
      F ≫ (fullSubcomplexOnVertices _ IsPullbackDiagramVertex).ι from
    (internalHomFlipHomEquiv Δ[n] (Δ[1] ⊗ Δ[1]) X).symm_apply_apply _]

/-- 元の終端分母から、一様な補完と境界照合に使う同じ全右辺・全上辺・全終端列を構成する。 -/
lemma exists_uniformTerminalRefinement {X : SSet.{u}} [Quasicategory X] [IsStable X]
    (P : SSet.{u}) {n : ℕ} (D : (Δ[n] : SSet.{u}) ⟶ X) (s : (Δ[1] : SSet.{u}) ⟶ X)
    (hs : s.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) =
      D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))) :
    ∃ F : (Δ[n] : SSet.{u}) ⟶ pullbackDiagrams X,
      F ≫ pullbackProjection X = simplexTerminalCospanFamily D s hs ∧
      F.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n)) =
        terminalPullbackColumnVertex s ∧
      squareRightEdge ≫ uniformTerminalRefinementSquare P F =
        internalHomFlipHomEquiv Δ[n] Δ[1] ((ihom P).obj X)
          (SSet.const (functorVertex (internalHomFlipHomEquiv P Δ[1] X
            (SSet.const (functorVertex s))))) ∧
      squareTopEdge ≫ uniformTerminalRefinementSquare P F =
        internalHomFlipHomEquiv Δ[n] Δ[1] ((ihom P).obj X)
          (simplexTerminalArrowFamily (D ≫ constantFunctorMap P X)) ∧
      uniformTerminalRefinementSquare P F ≫
        evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (Fin.last n)) =
        squareColumnDiagram (internalHomFlipHomEquiv P Δ[1] X
          (SSet.const (functorVertex s))) := by
  obtain ⟨F, hF, hlast⟩ := exists_simplexTerminalPullbackFamily D s hs
  refine ⟨F, hF, hlast, ?_, ?_, ?_⟩
  · rw [uniformTerminalRefinementSquare, ← Category.assoc,
      terminalRefinementSquare_right D s hs F hF,
      ← spanInternalHomFlip_post (constantFunctorMap P X), SSet.const_comp,
      spanInternalHomFlip_const (K := P) s]
    rfl
  · rw [uniformTerminalRefinementSquare, ← Category.assoc,
      terminalRefinementSquare_top D s hs F hF,
      ← spanInternalHomFlip_post (constantFunctorMap P X), ← simplexTerminalArrowFamily_post]
  · have ht : terminalRefinementSquare F ≫
        evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (Fin.last n)) = squareColumnDiagram s := by
      rw [terminalRefinementSquare_evaluate, hlast]
      exact Equiv.symm_apply_apply _ _
    have hn : (ihom (Δ[n] : SSet.{u})).map (constantFunctorMap P X) ≫
        evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (Fin.last n)) =
      evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (Fin.last n)) ≫ constantFunctorMap P X := rfl
    rw [uniformTerminalRefinementSquare, Category.assoc, hn, ← Category.assoc, ht,
      spanInternalHomFlip_const]
    exact Category.assoc _ _ _

/-- 完成族側の前段は、元の一つの実前段の定値族であり全パラメータで一様。 -/
lemma uniformTerminalRefinementSquare_prefix {X : SSet.{u}} [Quasicategory X] [IsStable X]
    (P : SSet.{u}) {n : ℕ} (F : (Δ[n] : SSet.{u}) ⟶ pullbackDiagrams X) :
    pullbackSourcePrefixFamily (parametricPullbackDiagramFamily
      (uniformTerminalRefinementSquare P F) (uniformTerminalRefinementSquare_isPullback P F)) =
      SSet.const (functorVertex (F ≫ (fullSubcomplexOnVertices _ IsPullbackDiagramVertex).ι ≫
        evaluateFunctorAt ((stdSimplex.obj₀Equiv.symm (0 : Fin 2)),
          (stdSimplex.obj₀Equiv.symm (0 : Fin 2))))) := by
  rw [uniformTerminalRefinementSquare_family, pullbackSourcePrefixFamily, SSet.const_comp]
  rfl

lemma verdierSpanFamilyDenominatorArrow_pre {A B : StableCategory.{u}} (i : ExactMap A B)
    (x z : B.obj _⦋0⦌) {S P : SSet.{u}} (j : S ⟶ P)
    (g : P ⟶ verdierDenominatorSpanFamily i x z) :
    verdierSpanFamilyDenominatorArrow i x z (j ≫ g) =
      j ≫ verdierSpanFamilyDenominatorArrow i x z g := by
  simp only [verdierSpanFamilyDenominatorArrow, Category.assoc]

/-- 完成族から回収した同じ実 fiber の分母は、元の一つの実分母図式で厳密に一定。 -/
lemma verdierSpanFamilyDenominatorArrow_fiber {A B : StableCategory.{u}} (i : ExactMap A B)
    (x z : B.obj _⦋0⦌) (d : (verdierDenominatorOver i x : SSet.{u}) _⦋0⦌)
    {K : SSet.{u}} (g : K ⟶ vertexFiber (verdierDenominatorSpanProjection i x z) d) :
    verdierSpanFamilyDenominatorArrow i x z
        (g ≫ vertexFiberι (verdierDenominatorSpanProjection i x z) d) =
      SSet.const (functorVertex ((joinStdSimplexIso 0 0).inv ≫ d.val.val)) := by
  have hp : (g ≫ vertexFiberι (verdierDenominatorSpanProjection i x z) d) ≫
      verdierDenominatorSpanProjection i x z = SSet.const d := by
    rw [Category.assoc, vertexFiberι_comp, SSet.comp_const]
  have he := congrArg (fun f => f ≫ (verdierDenominatorOver i x).ι ≫
    F2.Idempotent.pointSliceArrowMap (SSet.yonedaEquiv.symm x)) hp
  simp only [Category.assoc, SSet.const_comp] at he
  change verdierSpanFamilyDenominatorArrow i x z
      (g ≫ vertexFiberι (verdierDenominatorSpanProjection i x z) d) =
    SSet.const ((F2.Idempotent.pointSliceArrowMap (SSet.yonedaEquiv.symm x)).app
      (Opposite.op ⦋0⦌) d.val) at he
  rw [F2.Idempotent.pointSliceArrowMap_vertex] at he
  exact he

/-- 実相対回収円柱の始端分母は、完成族側の一様な同じ実分母へ厳密に戻る。 -/
lemma verdierRecoveredBoundaryDenominator_start {A B : StableCategory.{u}}
    (i : ExactMap A B) (x z : B.obj _⦋0⦌)
    (d : (verdierDenominatorOver i x : SSet.{u}) _⦋0⦌) {S K : SSet.{u}} (j : S ⟶ K)
    (g : K ⟶ vertexFiber (verdierDenominatorSpanProjection i x z) d)
    (a : S ⟶ verdierDenominatorSpanFamily i x z)
    (L : SSet.Homotopy (j ≫ g ≫ vertexFiberι (verdierDenominatorSpanProjection i x z) d) a) :
    (SSet.ι₀ : S ⟶ S ⊗ (Δ[1] : SSet.{u})) ≫
        verdierSpanFamilyDenominatorArrow i x z L.h =
      SSet.const (functorVertex ((joinStdSimplexIso 0 0).inv ≫ d.val.val)) := by
  have h₀ : (SSet.ι₀ : S ⟶ S ⊗ (Δ[1] : SSet.{u})) ≫ L.h =
      (j ≫ g) ≫ vertexFiberι (verdierDenominatorSpanProjection i x z) d := by
    simpa only [Category.assoc] using L.h₀
  rw [← verdierSpanFamilyDenominatorArrow_pre, h₀, verdierSpanFamilyDenominatorArrow_fiber]

/-- 同じ実円柱の終端は、元の境界分母族の全辺へ厳密に戻る。 -/
lemma verdierRecoveredBoundaryDenominator_end {A B : StableCategory.{u}}
    (i : ExactMap A B) (x z : B.obj _⦋0⦌) {S : SSet.{u}}
    {a b : S ⟶ verdierDenominatorSpanFamily i x z} (L : SSet.Homotopy a b) :
    (SSet.ι₁ : S ⟶ S ⊗ (Δ[1] : SSet.{u})) ≫
      verdierSpanFamilyDenominatorArrow i x z L.h =
      verdierSpanFamilyDenominatorArrow i x z b := by
  rw [← verdierSpanFamilyDenominatorArrow_pre, L.h₁]

/-- 回収された実分母図式の終点は、元の固定した終端頂点。 -/
lemma verdierDenominatorDiagram_target {A B : StableCategory.{u}} (i : ExactMap A B)
    (x : B.obj _⦋0⦌) (d : (verdierDenominatorOver i x : SSet.{u}) _⦋0⦌) :
    ((joinStdSimplexIso 0 0).inv ≫ d.val.val).app (Opposite.op ⦋0⦌)
      (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) = x := by
  have hv : stdSimplex.obj₀Equiv.symm (1 : Fin 2) =
      SSet.yonedaEquiv (stdSimplex.δ (0 : Fin 2) : (Δ[0] : SSet.{u}) ⟶ Δ[1]) := by decide
  rw [hv, ← SSet.yonedaEquiv_comp, ← joinStdSimplexIso_zero_inr,
    Category.assoc, Iso.hom_inv_id_assoc, d.val.property, Equiv.apply_symm_apply]

/-- 実回収円柱の始端に、一つの前段を共有する補完と相対 corner の同じ二脚を構成する。 -/
lemma exists_verdierRecoveredStartBoundary
    {A B : StableCategory.{u}} (i : ExactMap A B) {n : ℕ} (D : (Δ[n] : SSet.{u}) ⟶ B.obj)
    (z : B.obj _⦋0⦌)
    (d : (verdierDenominatorOver i
      (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))) : SSet.{u}) _⦋0⦌)
    {S K : SSet.{u}} (j : S ⟶ K)
    (g : K ⟶ vertexFiber (verdierDenominatorSpanProjection i
      (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))) z) d)
    (a : S ⟶ verdierDenominatorSpanFamily i
      (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))) z)
    (L : SSet.Homotopy (j ≫ g ≫ vertexFiberι (verdierDenominatorSpanProjection i
      (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))) z) d) a)
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
    ∃ F : (Δ[n] : SSet.{u}) ⟶ pullbackDiagrams B.obj,
      F ≫ pullbackProjection B.obj = simplexTerminalCospanFamily D
        ((joinStdSimplexIso 0 0).inv ≫ d.val.val) (verdierDenominatorDiagram_target i _ d) ∧
      F.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n)) =
        terminalPullbackColumnVertex ((joinStdSimplexIso 0 0).inv ≫ d.val.val) ∧
      (parametricPullbackDiagramFamily (uniformTerminalRefinementSquare S F)
          (uniformTerminalRefinementSquare_isPullback S F) ≫
          (ihom (Δ[n] : SSet.{u})).map (pullbackProjection B.obj) =
        (SSet.ι₀ : S ⟶ S ⊗ (Δ[1] : SSet.{u})) ≫ parametricPullbackDiagramFamily Q hQ ≫
          (ihom (Δ[n] : SSet.{u})).map (pullbackProjection B.obj)) ∧
      (parametricPullbackDiagramFamily (uniformTerminalRefinementSquare S F)
          (uniformTerminalRefinementSquare_isPullback S F) ≫
          (pre (simplexLastPoint n)).app (pullbackDiagrams B.obj) =
        (SSet.ι₀ : S ⟶ S ⊗ (Δ[1] : SSet.{u})) ≫ parametricPullbackDiagramFamily Q hQ ≫
          (pre (simplexLastPoint n)).app (pullbackDiagrams B.obj)) ∧
      parametricPullbackDiagramFamily (uniformTerminalRefinementSquare S F)
        (uniformTerminalRefinementSquare_isPullback S F) = SSet.const (functorVertex F) := by
  let x := D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))
  let s := (joinStdSimplexIso 0 0).inv ≫ d.val.val
  obtain ⟨F, hF, hlast, hRr, hRt, hRl⟩ :=
    exists_uniformTerminalRefinement S D s (verdierDenominatorDiagram_target i x d)
  have h₀ := verdierRecoveredBoundaryDenominator_start i x z d j g a L
  have hr : squareRightEdge ≫ uniformTerminalRefinementSquare S F =
      internalHomFlipHomEquiv Δ[n] Δ[1] ((ihom S).obj B.obj)
        (SSet.const (functorVertex (internalHomFlipHomEquiv S Δ[1] B.obj
          ((SSet.ι₀ : S ⟶ S ⊗ (Δ[1] : SSet.{u})) ≫
            verdierSpanFamilyDenominatorArrow i x z L.h)))) := by
    rw [h₀]
    exact hRr
  have hl : uniformTerminalRefinementSquare S F ≫
      evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (Fin.last n)) =
      squareColumnDiagram (internalHomFlipHomEquiv S Δ[1] B.obj
        ((SSet.ι₀ : S ⟶ S ⊗ (Δ[1] : SSet.{u})) ≫
          verdierSpanFamilyDenominatorArrow i x z L.h)) := by
    rw [h₀]
    exact hRl
  obtain ⟨hb, ht⟩ := terminalRefinementBoundary_projections
    (SSet.ι₀ : S ⟶ S ⊗ (Δ[1] : SSet.{u})) D
    (verdierSpanFamilyDenominatorArrow i x z L.h) Q (uniformTerminalRefinementSquare S F)
    hQ (uniformTerminalRefinementSquare_isPullback S F) hQr hr hQt hRt hQl hl
  exact ⟨F, hF, hlast, hb, ht, uniformTerminalRefinementSquare_family S F⟩

end SerrePositivity.KST.LocalizingInvariants
