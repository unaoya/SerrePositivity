module

public import SerrePositivity.KST.LocalizingInvariants.VerdierSimplexTerminalRefinement
public import SerrePositivity.KST.LocalizingInvariants.StableFunctorMaps
public import SerrePositivity.KST.LocalizingInvariants.VerdierSpanCanonicalEdges
public import SerrePositivity.KST.LocalizingInvariants.CoconeFamilyTranspose
public import SerrePositivity.KST.LocalizingInvariants.VerdierCompletedSpanRelativeRecovery

/-!
概要：動く実分母の全パラメータに沿って、前段全体の終端 pullback を同時に取る。
方針：安定関手圏で元の列四角形を厳密に固定し、二段の評価で実分母性を証明する。
規約：パラメータ族は定値にしない。終端の分母は元の同じ全族として保持する。
使われ方：実分数の境界輸送円柱から前段全体の実輸送を構成する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.Fibration
namespace SerrePositivity.KST.LocalizingInvariants

/-- 終端の列四角形を固定した精密化。分母条件を使う前の実普遍図式。 -/
lemma exists_simplexTerminalRefinementSquare {X : SSet.{u}}
    [Quasicategory X] [IsStable X] {n : ℕ} (D : (Δ[n] : SSet.{u}) ⟶ X)
    (s : (Δ[1] : SSet.{u}) ⟶ X)
    (hs : s.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) =
      D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))) :
    ∃ Q : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ (ihom (Δ[n] : SSet.{u})).obj X,
      IsPullbackSquare Q ∧ squareVertex Q 0 1 = functorVertex D ∧
      Q ≫ evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (Fin.last n)) = squareColumnDiagram s ∧
      (∀ k : (Δ[n] : SSet.{u}) _⦋0⦌, squareRightEdge ≫ Q ≫ evaluateFunctorAt k = s) ∧
      squareRightEdge ≫ Q = internalHomFlipHomEquiv Δ[n] Δ[1] X
        (SSet.const (functorVertex s)) ∧
      squareTopEdge ≫ Q = internalHomFlipHomEquiv Δ[n] Δ[1] X
        (simplexTerminalArrowFamily D) := by
  obtain ⟨F, hF, hlast⟩ := exists_simplexTerminalPullbackFamily D s hs
  refine ⟨terminalRefinementSquare F,
    terminalRefinementSquare_isPullback (B := ⟨X, inferInstance, inferInstance⟩) F,
    terminalRefinementSquare_original D s hs F hF, ?_, ?_,
    terminalRefinementSquare_right D s hs F hF,
    terminalRefinementSquare_top D s hs F hF⟩
  · rw [terminalRefinementSquare_evaluate, hlast]
    exact Equiv.symm_apply_apply _ _
  · intro k
    exact terminalRefinementSquare_right_evaluate D s hs F hF k

/-- 任意の動く分母族を使う同時精密化。全点の分母性も元の実 pullback から証明する。 -/
lemma exists_verdierParametricTerminalRefinement
    {A B C : StableCategory.{u}} {i : ExactMap A B} {q : ExactMap B C}
    (h : IsVerdierSequence i q) {P : SSet.{u}} {n : ℕ}
    (D : (Δ[n] : SSet.{u}) ⟶ (ihom P).obj B.obj)
    (s : (Δ[1] : SSet.{u}) ⟶ (ihom P).obj B.obj)
    (hs : s.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) =
      D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n)))
    (hW : ∀ p : P _⦋0⦌,
      SSet.yonedaEquiv (s ≫ evaluateFunctorAt p) ∈ weakEquivalences i) :
    ∃ Q : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶
        (ihom (Δ[n] : SSet.{u})).obj ((ihom P).obj B.obj),
      IsPullbackSquare Q ∧ squareVertex Q 0 1 = functorVertex D ∧
      Q ≫ evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (Fin.last n)) = squareColumnDiagram s ∧
      (∀ k : (Δ[n] : SSet.{u}) _⦋0⦌, squareRightEdge ≫ Q ≫ evaluateFunctorAt k = s) ∧
      squareRightEdge ≫ Q = internalHomFlipHomEquiv Δ[n] Δ[1] ((ihom P).obj B.obj)
        (SSet.const (functorVertex s)) ∧
      squareTopEdge ≫ Q = internalHomFlipHomEquiv Δ[n] Δ[1] ((ihom P).obj B.obj)
        (simplexTerminalArrowFamily D) ∧
      ∀ (k : (Δ[n] : SSet.{u}) _⦋0⦌) (p : P _⦋0⦌),
        (squareLeftArrow (Q ≫ evaluateFunctorAt k ≫ evaluateFunctorAt p)).edge ∈
          weakEquivalences i := by
  have : IsStable ((ihom P).obj B.obj) := (stableFunctorCategory P B).isStable
  have : HasFiniteLimits ((ihom P).obj B.obj) := hasFiniteLimits_of_isStable _
  have : HasFiniteLimits B.obj := hasFiniteLimits_of_isStable _
  obtain ⟨Q, hQ, hD, hlast, hright, hrightAll, htop⟩ :=
    exists_simplexTerminalRefinementSquare D s hs
  refine ⟨Q, hQ, hD, hlast, hright, hrightAll, htop, ?_⟩
  intro k p
  have hK := (isPullbackSquare_functor_iff Q).mp hQ k
  have hP := (isPullbackSquare_functor_iff (Q ≫ evaluateFunctorAt k)).mp hK p
  apply (weakEquivalences_pullback_iff h
    (Q ≫ evaluateFunctorAt k ≫ evaluateFunctorAt p) hP).mpr
  have he : squareRightEdge ≫ (Q ≫ evaluateFunctorAt k ≫ evaluateFunctorAt p) =
      s ≫ evaluateFunctorAt p := by
    simpa only [Category.assoc] using
      congrArg (fun f => f ≫ evaluateFunctorAt (Y := B.obj) p) (hright k)
  rw [squareRightArrow_edge, he]
  exact hW p

/-- 転置された全辺族の各評価は、元の同じ族の頂点を表す実辺。 -/
lemma spanTransposeFamily_evaluate {P L X : SSet.{u}}
    (f : P ⟶ (ihom L).obj X) (p : P _⦋0⦌) :
    internalHomFlipHomEquiv P L X f ≫ evaluateFunctorAt p =
      (functorVertexEquiv L X).symm (f.app (Opposite.op ⦋0⦌) p) := by
  have h := internalHomFlipHomEquiv_app_zero (internalHomFlipHomEquiv P L X f) p
  have he : internalHomFlipHomEquiv L P X (internalHomFlipHomEquiv P L X f) = f :=
    (internalHomFlipHomEquiv P L X).symm_apply_apply f
  rw [he] at h
  apply functorVertex_injective
  rw [← h]
  exact ((functorVertexEquiv L X).apply_symm_apply _).symm

/-- 実 slice の分母族を、同じパラメータ関手圏の実辺として保持する。 -/
def verdierDenominatorFamilyEdge {A B : StableCategory.{u}} (i : ExactMap A B)
    (x : B.obj _⦋0⦌) {P : SSet.{u}} (a : P ⟶ (verdierDenominatorOver i x : SSet.{u})) :
    (Δ[1] : SSet.{u}) ⟶ (ihom P).obj B.obj :=
  internalHomFlipHomEquiv P Δ[1] B.obj
    (a ≫ (verdierDenominatorOver i x).ι ≫
      F2.Idempotent.pointSliceArrowMap (SSet.yonedaEquiv.symm x))

lemma verdierDenominatorFamilyEdge_target {A B : StableCategory.{u}} (i : ExactMap A B)
    (x : B.obj _⦋0⦌) {P : SSet.{u}} (a : P ⟶ (verdierDenominatorOver i x : SSet.{u})) :
    (verdierDenominatorFamilyEdge i x a).app (Opposite.op ⦋0⦌)
      (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) = functorVertex (SSet.const x : P ⟶ B.obj) := by
  rw [verdierDenominatorFamilyEdge, internalHomFlipHomEquiv_app_zero,
    Category.assoc, Category.assoc, spanPointSliceArrowMap_target,
    SSet.comp_const, SSet.comp_const]
  congr 2
  have hp : stdSimplex.obj₀Equiv.symm (0 : Fin 1) =
      SSet.yonedaEquiv (𝟙 (Δ[0] : SSet.{u})) := by decide
  rw [hp, ← SSet.yonedaEquiv_comp, Category.id_comp, Equiv.apply_symm_apply]

lemma verdierDenominatorFamilyEdge_mem {A B : StableCategory.{u}} (i : ExactMap A B)
    (x : B.obj _⦋0⦌) {P : SSet.{u}} (a : P ⟶ (verdierDenominatorOver i x : SSet.{u}))
    (p : P _⦋0⦌) :
    SSet.yonedaEquiv (verdierDenominatorFamilyEdge i x a ≫ evaluateFunctorAt p) ∈
      weakEquivalences i := by
  rw [verdierDenominatorFamilyEdge, spanTransposeFamily_evaluate]
  change SSet.yonedaEquiv ((functorVertexEquiv Δ[1] B.obj).symm
    ((F2.Idempotent.pointSliceArrowMap (SSet.yonedaEquiv.symm x)).app (Opposite.op ⦋0⦌)
      (a.app (Opposite.op ⦋0⦌) p).val)) ∈ _
  rw [F2.Idempotent.pointSliceArrowMap_vertex]
  change SSet.yonedaEquiv ((functorVertexEquiv Δ[1] B.obj).symm
    ((functorVertexEquiv Δ[1] B.obj)
      ((joinStdSimplexIso 0 0).inv ≫ (a.app (Opposite.op ⦋0⦌) p).val.val))) ∈ _
  rw [Equiv.symm_apply_apply]
  exact fullSubcomplexOnVertices_vertex (a.app (Opposite.op ⦋0⦌) p)

/-- 境界輸送円柱を含む任意の実分母族から、前段全体の同じ全 pullback 族を構成する。 -/
lemma exists_verdierDenominatorFamilyTerminalRefinement
    {A B C : StableCategory.{u}} {i : ExactMap A B} {q : ExactMap B C}
    (h : IsVerdierSequence i q) {P : SSet.{u}} {n : ℕ} (D : (Δ[n] : SSet.{u}) ⟶ B.obj)
    (a : P ⟶ (verdierDenominatorOver i
      (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))) : SSet.{u})) :
    ∃ Q : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶
        (ihom (Δ[n] : SSet.{u})).obj ((ihom P).obj B.obj),
      IsPullbackSquare Q ∧ squareVertex Q 0 1 = functorVertex (D ≫ curry (snd P B.obj)) ∧
      Q ≫ evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (Fin.last n)) =
        squareColumnDiagram (verdierDenominatorFamilyEdge i
          (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))) a) ∧
      (∀ k : (Δ[n] : SSet.{u}) _⦋0⦌, squareRightEdge ≫ Q ≫ evaluateFunctorAt k =
        verdierDenominatorFamilyEdge i
          (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))) a) ∧
      squareRightEdge ≫ Q = internalHomFlipHomEquiv Δ[n] Δ[1] ((ihom P).obj B.obj)
        (SSet.const (functorVertex (verdierDenominatorFamilyEdge i
          (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))) a))) ∧
      squareTopEdge ≫ Q = internalHomFlipHomEquiv Δ[n] Δ[1] ((ihom P).obj B.obj)
        (simplexTerminalArrowFamily (D ≫ curry (snd P B.obj))) ∧
      ∀ (k : (Δ[n] : SSet.{u}) _⦋0⦌) (p : P _⦋0⦌),
        (squareLeftArrow (Q ≫ evaluateFunctorAt k ≫ evaluateFunctorAt p)).edge ∈
          weakEquivalences i := by
  apply exists_verdierParametricTerminalRefinement h (D ≫ curry (snd P B.obj))
    (verdierDenominatorFamilyEdge i _ a)
  · rw [verdierDenominatorFamilyEdge_target]
    exact (constantFunctorMap_vertex P _).symm
  · exact verdierDenominatorFamilyEdge_mem i _ a

/-- 元の有限商 Hom 族の実境界輸送から、前段全体の同じ分母 pullback 族まで回収する。 -/
lemma exists_verdierRelativeMappingBoundaryRefinement
    {A B C : StableCategory.{u}} {i : ExactMap A B} {q : ExactMap B C}
    (h : IsVerdierSequence i q) {n : ℕ} (D : (Δ[n] : SSet.{u}) ⟶ B.obj)
    (z : B.obj _⦋0⦌) {K : SSet.{u}} [K.Finite] (S : K.Subcomplex) [S.toSSet.Finite]
    (a : S.toSSet ⟶ verdierDenominatorSpanFamily i
      (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))) z)
    (f : K ⟶ intervalMappingSpace
      (q.hom.app (Opposite.op ⦋0⦌)
        (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))))
      (q.hom.app (Opposite.op ⦋0⦌) z))
    (ha : a ≫ verdierDenominatorSpanCanonicalComparison i
        (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))) z ≫
      fixedFractionEvaluation q.hom (weakEquivalences i) h.inverts
        (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))) z = S.ι ≫ f) :
    ∃ d : (verdierDenominatorOver i
        (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))) : SSet.{u}) _⦋0⦌,
      ∃ g : K ⟶ vertexFiber (verdierDenominatorSpanProjection i
          (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))) z) d,
      ∃ L : SSet.Homotopy
          (S.ι ≫ g ≫ vertexFiberι (verdierDenominatorSpanProjection i
            (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))) z) d) a,
      ∃ G : SSet.Homotopy
          (g ≫ vertexFiberι (verdierDenominatorSpanProjection i
              (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))) z) d ≫
            verdierDenominatorSpanCanonicalComparison i
              (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))) z ≫
            fixedFractionEvaluation q.hom (weakEquivalences i) h.inverts
              (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))) z) f,
        (S.ι ▷ (Δ[1] : SSet.{u})) ≫ G.h = L.h ≫
          verdierDenominatorSpanCanonicalComparison i
            (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))) z ≫
          fixedFractionEvaluation q.hom (weakEquivalences i) h.inverts
            (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))) z ∧
        ∃ Q : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶
            (ihom (Δ[n] : SSet.{u})).obj ((ihom (S.toSSet ⊗ (Δ[1] : SSet.{u}))).obj B.obj),
          IsPullbackSquare Q ∧
          squareVertex Q 0 1 = functorVertex (D ≫ curry (snd (S.toSSet ⊗ Δ[1]) B.obj)) ∧
          Q ≫ evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (Fin.last n)) =
            squareColumnDiagram (verdierDenominatorFamilyEdge i
              (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n)))
              (L.h ≫ verdierDenominatorSpanProjection i
                (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))) z)) ∧
          (∀ k : (Δ[n] : SSet.{u}) _⦋0⦌, squareRightEdge ≫ Q ≫ evaluateFunctorAt k =
            verdierDenominatorFamilyEdge i
              (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n)))
              (L.h ≫ verdierDenominatorSpanProjection i
                (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))) z)) ∧
          squareRightEdge ≫ Q = internalHomFlipHomEquiv Δ[n] Δ[1]
            ((ihom (S.toSSet ⊗ (Δ[1] : SSet.{u}))).obj B.obj)
            (SSet.const (functorVertex (verdierDenominatorFamilyEdge i
              (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n)))
              (L.h ≫ verdierDenominatorSpanProjection i
                (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))) z)))) ∧
          squareTopEdge ≫ Q = internalHomFlipHomEquiv Δ[n] Δ[1]
            ((ihom (S.toSSet ⊗ (Δ[1] : SSet.{u}))).obj B.obj)
            (simplexTerminalArrowFamily (D ≫ curry (snd (S.toSSet ⊗ Δ[1]) B.obj))) ∧
          ∀ (k : (Δ[n] : SSet.{u}) _⦋0⦌) (p : (S.toSSet ⊗ (Δ[1] : SSet.{u})) _⦋0⦌),
            (squareLeftArrow (Q ≫ evaluateFunctorAt k ≫ evaluateFunctorAt p)).edge ∈
              weakEquivalences i := by
  let x := D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))
  obtain ⟨d, g, L, G, hG⟩ := verdierFiniteMappingFamily_relative_recovery h x z S a f ha
  obtain ⟨Q, hQ, hD, hlast, hright, hrightAll, htop, hW⟩ :=
    exists_verdierDenominatorFamilyTerminalRefinement h D
      (L.h ≫ verdierDenominatorSpanProjection i x z)
  exact ⟨d, g, L, G, hG, Q, hQ, hD, hlast, hright, hrightAll, htop, hW⟩

end SerrePositivity.KST.LocalizingInvariants
