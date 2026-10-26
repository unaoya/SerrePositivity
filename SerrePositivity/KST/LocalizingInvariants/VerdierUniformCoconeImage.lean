module

public import SerrePositivity.KST.LocalizingInvariants.VerdierUniformSpanPrefixPath
public import SerrePositivity.KST.LocalizingInvariants.IntervalMappingCoconeExtension
public import SerrePositivity.KST.LocalizingInvariants.CoconeFamilyCoreCriterion

/-!
概要：同じ実分数評価の全比較を、元の商余錐を終端に固定した全余錐比較へ延長する。
方針：元の固定端点 Hom の実円柱を、前段と次辺の全 attachment 充填へ実代入する。
規約：指定された全 Homotopy・元の全商余錐・全時刻の前段と頂点を保持する。
使われ方：完成境界から回収した実全余錐を元の商全余錐と比較する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories SerrePositivity.KST.Fibration
namespace SerrePositivity.KST.LocalizingInvariants
variable {A B C : StableCategory.{u}} {i : ExactMap A B} {q : ExactMap B C}
  {h : IsVerdierSequence i q} {n : ℕ} {D : (Δ[n] : SSet.{u}) ⟶ B.obj}
  {z : B.obj _⦋0⦌} {K : SSet.{u}}
  {d : (verdierDenominatorOver i
    (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))) : SSet.{u}) _⦋0⦌}
  {g : K ⟶ vertexFiber (verdierDenominatorSpanProjection i
    (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))) z) d}
  {f : K ⟶ intervalMappingSpace
    (q.hom.app (Opposite.op ⦋0⦌)
      (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))))
    (q.hom.app (Opposite.op ⦋0⦌) z)}

/-- 元の商 Hom 比較円柱と終端の全商余錐を保持する、同じ全余錐円柱。 -/
structure VerdierUniformCoconeImage
    (L : SSet.Homotopy
      (g ≫ vertexFiberι (verdierDenominatorSpanProjection i
        (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))) z) d ≫
        verdierDenominatorSpanCanonicalComparison i
          (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))) z ≫
        fixedFractionEvaluation q.hom (weakEquivalences i) h.inverts
          (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))) z) f)
    (G : K ⟶ (ihom (join (Δ[n] : SSet.{u}) Δ[0])).obj C.obj) where
  whole : K ⊗ (Δ[1] : SSet.{u}) ⟶ (ihom (join (Δ[n] : SSet.{u}) Δ[0])).obj C.obj
  endpoint : (SSet.ι₁ : K ⟶ K ⊗ (Δ[1] : SSet.{u})) ≫ whole = G
  fixedPrefix : whole ≫ (pre (joinInl (Δ[n] : SSet.{u}) Δ[0])).app C.obj =
    SSet.const (functorVertex (D ≫ q.hom))
  lastArrow : whole ≫ (pre (joinMap (simplexLastPoint n) (𝟙 Δ[0]))).app C.obj =
    L.h ≫ vertexFiberι ((pre (boundary 1).ι).app C.obj)
      (functorVertex (intervalMappingBoundary
        (q.hom.app (Opposite.op ⦋0⦌)
          (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))))
        (q.hom.app (Opposite.op ⦋0⦌) z))) ≫
      (pre (joinStdSimplexIso 0 0).hom).app C.obj
  fixedApex : whole ≫ evaluateFunctorAt ((joinInr (Δ[n] : SSet.{u}) Δ[0]).app (Opposite.op ⦋0⦌)
    (stdSimplex.obj₀Equiv.symm (0 : Fin 1))) = SSet.const (q.hom.app (Opposite.op ⦋0⦌) z)

lemma exists_verdierUniformCoconeImage
    (L : SSet.Homotopy
      (g ≫ vertexFiberι (verdierDenominatorSpanProjection i
        (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))) z) d ≫
        verdierDenominatorSpanCanonicalComparison i
          (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))) z ≫
        fixedFractionEvaluation q.hom (weakEquivalences i) h.inverts
          (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))) z) f)
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
    Nonempty (VerdierUniformCoconeImage (h := h) L G) := by
  obtain ⟨U, he, hp, hn, hz⟩ := exists_relative_intervalMappingCoconeFamily
    (D ≫ q.hom) (q.hom.app (Opposite.op ⦋0⦌) z) (SSet.ι₁ : K ⟶ K ⊗ Δ[1]) G
    L.h hG (by
      rw [← Category.assoc (SSet.ι₁ : K ⟶ K ⊗ Δ[1]) L.h,
        L.h₁]
      exact hGe.symm)
  exact ⟨⟨U, he, hp, hn, hz⟩⟩


namespace VerdierUniformCoconeImage
variable {L : SSet.Homotopy
    (g ≫ vertexFiberι (verdierDenominatorSpanProjection i
      (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))) z) d ≫
      verdierDenominatorSpanCanonicalComparison i
        (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))) z ≫
      fixedFractionEvaluation q.hom (weakEquivalences i) h.inverts
        (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))) z) f}
  {G : K ⟶ (ihom (join (Δ[n] : SSet.{u}) Δ[0])).obj C.obj}
  (U : VerdierUniformCoconeImage (h := h) L G)

/-- 同じ全商円柱の始端。 -/
def initialFamily : K ⟶ (ihom (join (Δ[n] : SSet.{u}) Δ[0])).obj C.obj :=
  (SSet.ι₀ : K ⟶ K ⊗ (Δ[1] : SSet.{u})) ≫ U.whole

lemma initialFamily_prefix : U.initialFamily ≫
    (pre (joinInl (Δ[n] : SSet.{u}) Δ[0])).app C.obj =
      SSet.const (functorVertex (D ≫ q.hom)) := by
  rw [initialFamily, Category.assoc, U.fixedPrefix, SSet.comp_const]

/-- 同じ指定円柱が与える、元の商余錐への全 Homotopy。 -/
def homotopy : SSet.Homotopy U.initialFamily G where
  h := U.whole
  h₀ := rfl
  h₁ := U.endpoint
  rel := by ext m s; exact False.elim s.1.property

lemma invertsAllEdges : InvertsEdges U.whole Set.univ := by
  apply coconeFamily_invertsAllEdges_of_prefix_apex _ _ _ U.fixedApex
  rw [U.fixedPrefix]
  exact invertsEdges_const _ _ _ Set.univ

/-- 同じ全商円柱の各頂点の辺は可逆であり、元の全余錐への全関手同型を与える。 -/
def iso : FunctorIso U.initialFamily G := by
  apply functorIsoOfPointwiseInvertibleHomotopy U.homotopy
  intro k
  let e := (Truncated.Edge.id (X := (truncation 2).obj K) k).tensor homotopyIntervalEdge
  exact (isInvertibleEdge_congr
    (e := (simplicialHomotopyVertexEdge U.homotopy k).toTruncated)
    (f := (edgeOfSimplex e.edge).map ((truncation 2).map U.whole)) rfl).mpr
      (U.invertsAllEdges (Set.mem_univ e.edge))

/-- 同じ商円柱始端の次辺は、保存済み実 K 全族の同じ分数二胞体の上辺。 -/
lemma initialFamily_last : U.initialFamily ≫
    (pre (joinMap (simplexLastPoint n) (𝟙 Δ[0]))).app C.obj =
    (g ≫ vertexFiberι (verdierDenominatorSpanProjection i
      (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))) z) d ≫
      verdierSpanEvaluationSquare h
        (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))) z ≫
      (pre squareTopEdge).app C.obj) ≫ (pre (joinStdSimplexIso 0 0).hom).app C.obj := by
  rw [initialFamily, Category.assoc, U.lastArrow]
  have he := congrArg (fun v => g ≫ vertexFiberι (verdierDenominatorSpanProjection i
      (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))) z) d ≫
      v ≫ (pre (joinStdSimplexIso 0 0).hom).app C.obj)
    (verdierSpanEvaluationSquare_top h
      (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))) z)
  simp only [Category.assoc] at he ⊢
  rw [he, ← Category.assoc (SSet.ι₀ : K ⟶ K ⊗ Δ[1]) L.h,
    L.h₀]
  simp only [Category.assoc]

end VerdierUniformCoconeImage
end SerrePositivity.KST.LocalizingInvariants
