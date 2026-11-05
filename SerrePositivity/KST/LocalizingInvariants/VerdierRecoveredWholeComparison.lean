module

public import SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierFiniteMappingCoconeRecovery
public import SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierChosenTerminalRefinementMap
public import SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierSimplexParametricComparison

/-!
概要：両端円柱で選んだ同じ一様前段・同じ実全族を、元の商余錐の全比較へ接続する。
方針：保存した同じ pullback 補完から前段分母を回収し、元の分数比較円柱を実適用する。
規約：前段・実分母・次辺族を選び直さず、指定前段辺と固定頂点経路を保持する。
使われ方：相対有限全族回収と元の全商図式の比較を同じ実持ち上げに揃える。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped _root_.Simplicial
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

/-- 元の相対回収で選んだ実全族と、元の商余錐との同じ前段分母を持つ全比較。 -/
structure VerdierRecoveredWholeComparison (r : VerdierFiniteMappingCoconeRecovery h D z S a f)
    (G : K ⟶ (ihom (join (Δ[n] : SSet.{u}) Δ[0])).obj C.obj) where
  denominator : Truncated.Edge (X := (truncation 2).obj ((ihom (Δ[n] : SSet.{u})).obj B.obj))
    (functorVertex (terminalRefinementSourceDiagram r.cylinder.single)) (functorVertex D)
  denominator_mem : denominator.edge ∈ (relativeFirstRowSimplex q n).obj (Opposite.op ⦋1⦌)
  denominator_last : (evaluateFunctorAt (Y := B.obj)
    (stdSimplex.obj₀Equiv.symm (Fin.last n))).app (Opposite.op ⦋1⦌) denominator.edge =
    (roofPointSliceVertexEdge (SSet.yonedaEquiv.symm
      (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n)))) r.denominator.val).edge
  edge : Truncated.Edge
    (X := (truncation 2).obj ((ihom (join (Δ[n] : SSet.{u}) Δ[0])).obj ((ihom K).obj C.obj)))
    (functorVertex (internalHomFlipHomEquiv K (join (Δ[n] : SSet.{u}) Δ[0]) C.obj
      (r.cylinder.whole ≫ (ihom (join (Δ[n] : SSet.{u}) Δ[0])).map q.hom)))
    (functorVertex (internalHomFlipHomEquiv K (join (Δ[n] : SSet.{u}) Δ[0]) C.obj G))
  edge_invertible : IsInvertibleEdge
    (X := (ihom (join (Δ[n] : SSet.{u}) Δ[0])).obj ((ihom K).obj C.obj)) edge
  edge_prefix : ((pre (joinInl (Δ[n] : SSet.{u}) Δ[0])).app ((ihom K).obj C.obj)).app
    (Opposite.op ⦋1⦌) edge.edge = (spanConstantPrefixEdge K q.hom denominator).edge
  edge_apex : SSet.yonedaEquiv.symm edge.edge ≫ (pre (joinInr (Δ[n] : SSet.{u}) Δ[0])).app
    ((ihom K).obj C.obj) = curry (snd (Δ[0] : SSet.{u}) Δ[1] ≫
      SSet.const (functorVertex (SSet.const (q.hom.app (Opposite.op ⦋0⦌) z) : K ⟶ C.obj)))
  iso : FunctorIso (r.cylinder.whole ≫ (ihom (join (Δ[n] : SSet.{u}) Δ[0])).map q.hom) G

/-- 元の商 Hom 比較円柱を代入し、両端回収で選んだ同じ実全族の全比較を構成する。 -/
lemma exists_verdierRecoveredWholeComparison
    (r : VerdierFiniteMappingCoconeRecovery h D z S a f)
    (G : K ⟶ (ihom (join (Δ[n] : SSet.{u}) Δ[0])).obj C.obj)
    (hG : G ≫ (pre (joinInl (Δ[n] : SSet.{u}) Δ[0])).app C.obj =
      SSet.const (functorVertex (D ≫ q.hom)))
    (hGe : G ≫ (pre (joinMap (simplexLastPoint n) (𝟙 Δ[0]))).app C.obj =
      f ≫ vertexFiberι ((pre (boundary 1).ι).app C.obj)
        (functorVertex (intervalMappingBoundary
          (q.hom.app (Opposite.op ⦋0⦌)
            (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))))
          (q.hom.app (Opposite.op ⦋0⦌) z))) ≫
        (pre (joinStdSimplexIso 0 0).hom).app C.obj) :
    Nonempty (VerdierRecoveredWholeComparison r G) := by
  let x := D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))
  obtain ⟨t, ht, hlast⟩ := exists_verdierChosenTerminalRefinementMap h D r.denominator
    r.cylinder.single r.cylinder.single_projection r.cylinder.single_terminal
  have he : FunctorIso (verdierSpanEvaluatedMapping h x z r.denominator r.numerator) f :=
    functorIsoOfSimplicialHomotopy r.comparison
  have hp : r.cylinder.whole ≫ (pre (joinInl (Δ[n] : SSet.{u}) Δ[0])).app B.obj =
      SSet.const (functorVertex (terminalRefinementSourceDiagram r.cylinder.single)) :=
    r.cylinder.whole_prefix
  have hn : r.cylinder.whole ≫ (pre (joinMap (simplexLastPoint n) (𝟙 Δ[0]))).app B.obj =
      r.numerator ≫ verdierDenominatorSpanFiberArrow i x z r.denominator ≫
        (pre (joinStdSimplexIso 0 0).hom).app B.obj := by
    have hn := r.cylinder.whole_next
    simpa only [_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierSpanFamilyNumeratorArrow, _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierDenominatorSpanFiberArrow,
      Category.assoc] using hn
  obtain ⟨l, hi, hlp, hlv, ⟨e⟩⟩ := exists_verdierSimplexParametricComparison h D
    (terminalRefinementSourceDiagram r.cylinder.single) z t ht r.denominator hlast
    r.numerator r.cylinder.whole hp hn G hG f hGe he
  exact ⟨⟨t, ht, hlast, l, hi, hlp, hlv, e⟩⟩

/-- 元の有限商余錐族から、同じ実相対円柱と指定前段・頂点を保つ全比較を同時に回収する。 -/
lemma exists_verdierFiniteCoconeComparisonRecovery [K.Finite] [S.toSSet.Finite]
    (G : K ⟶ (ihom (join (Δ[n] : SSet.{u}) Δ[0])).obj C.obj)
    (hG : G ≫ (pre (joinInl (Δ[n] : SSet.{u}) Δ[0])).app C.obj =
      SSet.const (functorVertex (D ≫ q.hom)))
    (hz : G ≫ evaluateFunctorAt ((joinInr (Δ[n] : SSet.{u}) Δ[0]).app (Opposite.op ⦋0⦌)
      (stdSimplex.obj₀Equiv.symm (0 : Fin 1))) = SSet.const (q.hom.app (Opposite.op ⦋0⦌) z))
    (ha : a ≫ verdierDenominatorSpanCanonicalComparison i
        (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))) z ≫
      fixedFractionEvaluation q.hom (weakEquivalences i) h.inverts
        (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))) z =
      S.ι ≫ spanCoconeLastMapping (D ≫ q.hom) (q.hom.app (Opposite.op ⦋0⦌) z) G hG hz) :
    ∃ r : VerdierFiniteMappingCoconeRecovery h D z S a
        (spanCoconeLastMapping (D ≫ q.hom) (q.hom.app (Opposite.op ⦋0⦌) z) G hG hz),
      Nonempty (VerdierRecoveredWholeComparison r G) := by
  let fG := spanCoconeLastMapping (D ≫ q.hom) (q.hom.app (Opposite.op ⦋0⦌) z) G hG hz
  obtain ⟨r⟩ := exists_verdierFiniteMappingCoconeRecovery h D z S a fG ha
  have hGe := spanCoconeLastMapping_edge (D ≫ q.hom) (q.hom.app (Opposite.op ⦋0⦌) z) G hG hz
  exact ⟨r, exists_verdierRecoveredWholeComparison r G hG hGe⟩

end SerrePositivity.KST.LocalizingInvariants
