module

public import SerrePositivity.InfinityCategories.Stable.Quasicategory.CoconeFamilyTranspose
public import SerrePositivity.KST.LocalizingInvariants.CoconeFamilyCoreComparison
public import SerrePositivity.KST.LocalizingInvariants.SimplexAttachmentEquivalences
public import SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierRecoveredInitialPrefixPath

/-!
概要：保存済みの同じ実 K 全族と商全余錐円柱の始端を、指定二胞体付きで全図式比較する。
方針：構成済みの同じ前段辺と実分数比較辺を、証明済み共有全経路で直接貼り合わせる。
規約：前段補完・次辺族・分数評価二胞体を選び直さず、両制限に元の一次単体を保持する。
使われ方：指定 S 始端比較を保つ相対延長へ渡す、K 全体の実始端比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories SerrePositivity.KST.Fibration
namespace SerrePositivity.KST.LocalizingInvariants

variable {A B C : StableCategory.{u}} {i : ExactMap A B} {q : ExactMap B C}
  {h : IsVerdierSequence i q} {n : ℕ} {D : (Δ[n] : SSet.{u}) ⟶ B.obj}
  {z : B.obj _⦋0⦌} {K : SSet.{u}} {S : K.Subcomplex}
  {a : S.toSSet ⟶ verdierDenominatorSpanFamily i
    (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))) z}
  {f : K ⟶ intervalMappingSpace
    (q.hom.app (Opposite.op ⦋0⦌)
      (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))))
    (q.hom.app (Opposite.op ⦋0⦌) z)}
  {G : K ⟶ (ihom (join (Δ[n] : SSet.{u}) Δ[0])).obj C.obj}

local notation "J" => join (Δ[n] : SSet) Δ[0]

structure VerdierRecoveredInitialComparison
    (r : VerdierFiniteMappingCoconeRecovery h D z S a f)
    (U : VerdierRecoveredQuotientCoconeCylinder r G) where
  denominator : Truncated.Edge (X := (truncation 2).obj ((ihom (Δ[n] : SSet.{u})).obj B.obj))
    (functorVertex (terminalRefinementSourceDiagram r.cylinder.single)) (functorVertex D)
  denominator_mem : denominator.edge ∈ (relativeFirstRowSimplex q n).obj (Opposite.op ⦋1⦌)
  denominator_edge : denominator.edge =
    (squareLeftArrow (terminalRefinementSquare r.cylinder.single)).edge
  edge : Truncated.Edge (X := (truncation 2).obj ((ihom J).obj ((ihom K).obj C.obj)))
    (functorVertex (internalHomFlipHomEquiv K J C.obj (r.cylinder.whole ≫ (ihom J).map q.hom)))
    (functorVertex (internalHomFlipHomEquiv K J C.obj U.initialFamily))
  isInvertible : IsInvertibleEdge (X := (ihom J).obj ((ihom K).obj C.obj)) edge
  prefix_eq : ((pre (joinInl (Δ[n] : SSet.{u}) Δ[0])).app ((ihom K).obj C.obj)).app
    (Opposite.op ⦋1⦌) edge.edge = (spanConstantPrefixEdge K q.hom denominator).edge
  last_eq : ((pre (joinMap (simplexLastPoint n) (𝟙 Δ[0]))).app ((ihom K).obj C.obj)).app
      (Opposite.op ⦋1⦌) edge.edge =
    (((functorEdgeOfSimplicialHomotopy r.initialFractionHomotopy).map ((truncation 2).map
      ((pre (joinStdSimplexIso 0 0).hom).app ((ihom K).obj C.obj)))).edge)

lemma exists_verdierRecoveredInitialComparison
    (r : VerdierFiniteMappingCoconeRecovery h D z S a f)
    (U : VerdierRecoveredQuotientCoconeCylinder r G) :
    Nonempty (VerdierRecoveredInitialComparison r U) := by
  obtain ⟨t, ht, hraw, hai, hshared⟩ := exists_verdierRecoveredInitialPrefixPath r
  let F := internalHomFlipHomEquiv K J C.obj (r.cylinder.whole ≫ (ihom J).map q.hom)
  let T := internalHomFlipHomEquiv K J C.obj U.initialFamily
  let A₀ := spanConstantPrefixEdge K q.hom t
  let B₀ := (functorEdgeOfSimplicialHomotopy r.initialFractionHomotopy).map
    ((truncation 2).map ((pre (joinStdSimplexIso 0 0).hom).app ((ihom K).obj C.obj)))
  have hFp : joinInl (Δ[n] : SSet.{u}) Δ[0] ≫ F =
      (terminalRefinementSourceDiagram r.cylinder.single ≫ q.hom) ≫
        constantFunctorMap K C.obj := by
    dsimp only [F]
    rw [← internalHomFlipHomEquiv_pre_app, r.initialSource_prefix, spanInternalHomFlip_const]
    rfl
  have hTp : joinInl (Δ[n] : SSet.{u}) Δ[0] ≫ T =
      (D ≫ q.hom) ≫ constantFunctorMap K C.obj := by
    dsimp only [T]
    rw [← internalHomFlipHomEquiv_pre_app, U.initialFamily_prefix, spanInternalHomFlip_const]
    rfl
  let A' := A₀.ofEq (congrArg functorVertex hFp).symm (congrArg functorVertex hTp).symm
  let V := r.numerator ≫ vertexFiberι (verdierDenominatorSpanProjection i
    (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))) z) r.denominator ≫
    verdierSpanEvaluationSquare h
      (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))) z
  have hFB : joinMap (simplexLastPoint n) (𝟙 Δ[0]) ≫ F =
      (joinStdSimplexIso 0 0).hom ≫
        internalHomFlipHomEquiv K Δ[1] C.obj (V ≫ (pre squareBottomEdge).app C.obj) := by
    dsimp only [F]
    rw [← internalHomFlipHomEquiv_pre_app, r.initialSource_last,
      internalHomFlipHomEquiv_pre_app]
    rfl
  have hTB : joinMap (simplexLastPoint n) (𝟙 Δ[0]) ≫ T =
      (joinStdSimplexIso 0 0).hom ≫
        internalHomFlipHomEquiv K Δ[1] C.obj (V ≫ (pre squareTopEdge).app C.obj) := by
    dsimp only [T]
    rw [← internalHomFlipHomEquiv_pre_app, U.initialFamily_last,
      internalHomFlipHomEquiv_pre_app]
    rfl
  have hBs : functorVertex ((joinStdSimplexIso 0 0).hom ≫
      internalHomFlipHomEquiv K Δ[1] C.obj (V ≫ (pre squareBottomEdge).app C.obj)) =
      functorVertex (joinMap (simplexLastPoint n) (𝟙 Δ[0]) ≫ F) := by rw [hFB]
  have hBt : functorVertex ((joinStdSimplexIso 0 0).hom ≫
      internalHomFlipHomEquiv K Δ[1] C.obj (V ≫ (pre squareTopEdge).app C.obj)) =
      functorVertex (joinMap (simplexLastPoint n) (𝟙 Δ[0]) ≫ T) := by rw [hTB]
  let B' := (SSet.Edge.ofTruncated B₀).ofEq hBs hBt
  have hab : SSet.yonedaEquiv.symm A'.edge ≫
      (pre (simplexLastPoint n)).app ((ihom K).obj C.obj) =
      SSet.yonedaEquiv.symm B'.edge ≫
        (pre (joinInl (Δ[0] : SSet.{u}) Δ[0])).app ((ihom K).obj C.obj) := by
    change SSet.yonedaEquiv.symm A₀.edge ≫
      (pre (simplexLastPoint n)).app ((ihom K).obj C.obj) =
      SSet.yonedaEquiv.symm (((pre (joinStdSimplexIso 0 0).hom).app ((ihom K).obj C.obj)).app
        (Opposite.op ⦋1⦌) (functorEdgeOfSimplicialHomotopy r.initialFractionHomotopy).edge) ≫
        (pre (joinInl (Δ[0] : SSet.{u}) Δ[0])).app ((ihom K).obj C.obj)
    rw [← SSet.yonedaEquiv_symm_comp, Category.assoc, ← NatTrans.comp_app,
      ← pre_map, joinStdSimplexIso_zero_inl]
    exact hshared.symm
  have hb₀ : IsInvertibleEdge (functorEdgeOfSimplicialHomotopy r.initialFractionHomotopy) := by
    have hi := fractionFamilyComparison_isInvertible q.hom (weakEquivalences i) h.inverts
      (r.numerator ≫ vertexFiberι (verdierDenominatorSpanProjection i
        (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))) z) r.denominator ≫
        verdierDenominatorSpanCanonicalComparison i
          (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))) z ≫
        fixedMarkedSpanInclusion B.obj (weakEquivalences i)
          (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))) z)
    apply (isInvertibleEdge_congr (e := functorEdgeOfSimplicialHomotopy r.initialFractionHomotopy)
      (f := functorEdgeOfSimplicialHomotopy (spanSquareFamilyHomotopy
        ((r.numerator ≫ vertexFiberι (verdierDenominatorSpanProjection i
          (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))) z) r.denominator ≫
          verdierDenominatorSpanCanonicalComparison i
            (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))) z ≫
          fixedMarkedSpanInclusion B.obj (weakEquivalences i)
            (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))) z) ≫
          fractionEvaluationSquare q.hom (weakEquivalences i) h.inverts))) rfl).mpr hi
  obtain ⟨l, hlp, hln⟩ := exists_simplexAttachmentComparison n F T A'.toTruncated
    B'.toTruncated hab
  have hai' : IsInvertibleEdge (X := (ihom (Δ[n] : SSet.{u})).obj ((ihom K).obj C.obj))
      A'.toTruncated :=
    (isInvertibleEdge_congr (e := A₀.toTruncated) (f := A'.toTruncated) rfl).mp hai
  have hbi : IsInvertibleEdge
      (X := (ihom (join (Δ[0] : SSet.{u}) Δ[0])).obj ((ihom K).obj C.obj)) B'.toTruncated :=
    (isInvertibleEdge_congr (e := B₀) (f := B'.toTruncated) rfl).mp
      (hb₀.map ((pre (joinStdSimplexIso 0 0).hom).app ((ihom K).obj C.obj)))
  have hli := simplexAttachmentComparison_isInvertible n l
    ((isInvertibleEdge_congr hlp).mpr hai') ((isInvertibleEdge_congr hln).mpr hbi)
  exact ⟨⟨t, ht, hraw, l, hli, hlp, hln⟩⟩

def VerdierRecoveredInitialComparison.iso
    {r : VerdierFiniteMappingCoconeRecovery h D z S a f}
    {U : VerdierRecoveredQuotientCoconeCylinder r G}
    (c : VerdierRecoveredInitialComparison r U) :
    FunctorIso (r.cylinder.whole ≫ (ihom J).map q.hom) U.initialFamily := by
  have := c.isInvertible
  exact spanFunctorIsoUnflip (asIso (Truncated.HomotopyCategory.homMk c.edge))

end SerrePositivity.KST.LocalizingInvariants
