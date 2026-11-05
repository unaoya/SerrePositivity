module

public meta import SerrePositivity.InfinityCategories.Simplicial.DeprecatedAlias

public import SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierUniformSpanPrefixPath
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
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories SerrePositivity.KST.Fibration
namespace SerrePositivity.KST.LocalizingInvariants
end SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.LocalizingInvariants.VerdierUniformCoconeImage
end SerrePositivity.KST.LocalizingInvariants.VerdierUniformCoconeImage
namespace SerrePositivity.InfinityCategories.Derived.Verdier.Fractions
open SerrePositivity.KST.LocalizingInvariants
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
open _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierUniformCoconeImage
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
end SerrePositivity.InfinityCategories.Derived.Verdier.Fractions

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierUniformCoconeImage (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierUniformCoconeImage := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierUniformCoconeImage

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.exists_verdierUniformCoconeImage := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.exists_verdierUniformCoconeImage

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierUniformCoconeImage._sizeOf_1 (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierUniformCoconeImage._sizeOf_1 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierUniformCoconeImage._sizeOf_1

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierUniformCoconeImage._sizeOf_inst (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierUniformCoconeImage._sizeOf_inst := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierUniformCoconeImage._sizeOf_inst

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierUniformCoconeImage.casesOn (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierUniformCoconeImage.casesOn := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierUniformCoconeImage.casesOn

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierUniformCoconeImage.ctorIdx (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierUniformCoconeImage.ctorIdx := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierUniformCoconeImage.ctorIdx

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierUniformCoconeImage.endpoint := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierUniformCoconeImage.endpoint

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierUniformCoconeImage.fixedApex := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierUniformCoconeImage.fixedApex

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierUniformCoconeImage.fixedPrefix := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierUniformCoconeImage.fixedPrefix

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierUniformCoconeImage.homotopy (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierUniformCoconeImage.homotopy := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierUniformCoconeImage.homotopy

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierUniformCoconeImage.initialFamily (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierUniformCoconeImage.initialFamily := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierUniformCoconeImage.initialFamily

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierUniformCoconeImage.initialFamily_last := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierUniformCoconeImage.initialFamily_last

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierUniformCoconeImage.initialFamily_prefix := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierUniformCoconeImage.initialFamily_prefix

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierUniformCoconeImage.invertsAllEdges := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierUniformCoconeImage.invertsAllEdges

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierUniformCoconeImage.iso (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierUniformCoconeImage.iso := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierUniformCoconeImage.iso

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierUniformCoconeImage.lastArrow := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierUniformCoconeImage.lastArrow

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierUniformCoconeImage.mk (since := "2026-11-05"), match_pattern]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierUniformCoconeImage.mk := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierUniformCoconeImage.mk

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierUniformCoconeImage.noConfusion (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierUniformCoconeImage.noConfusion := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierUniformCoconeImage.noConfusion

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierUniformCoconeImage.noConfusionType (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierUniformCoconeImage.noConfusionType := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierUniformCoconeImage.noConfusionType

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierUniformCoconeImage.rec (since := "2026-11-05"), elab_as_elim]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierUniformCoconeImage.rec := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierUniformCoconeImage.rec

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierUniformCoconeImage.recOn (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierUniformCoconeImage.recOn := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierUniformCoconeImage.recOn

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierUniformCoconeImage.whole (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierUniformCoconeImage.whole := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierUniformCoconeImage.whole

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierUniformCoconeImage.homotopy._proof_1 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierUniformCoconeImage.homotopy._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierUniformCoconeImage.homotopy._proof_2 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierUniformCoconeImage.homotopy._proof_2

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierUniformCoconeImage.initialFamily.eq_1 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierUniformCoconeImage.initialFamily.eq_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierUniformCoconeImage.iso._proof_1 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierUniformCoconeImage.iso._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierUniformCoconeImage.iso._proof_2 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierUniformCoconeImage.iso._proof_2

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierUniformCoconeImage.mk._flat_ctor (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierUniformCoconeImage.mk._flat_ctor := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierUniformCoconeImage.mk._flat_ctor

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierUniformCoconeImage.mk.inj := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierUniformCoconeImage.mk.inj

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierUniformCoconeImage.mk.injEq := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierUniformCoconeImage.mk.injEq

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierUniformCoconeImage.mk.noConfusion (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierUniformCoconeImage.mk.noConfusion := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierUniformCoconeImage.mk.noConfusion

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierUniformCoconeImage.mk.sizeOf_spec := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierUniformCoconeImage.mk.sizeOf_spec
