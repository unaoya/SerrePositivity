module

public meta import SerrePositivity.InfinityCategories.Simplicial.DeprecatedAlias

public import SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierSpanCanonicalEdges
public import SerrePositivity.KST.LocalizingInvariants.VerdierSimplexRefinementCocone
public import SerrePositivity.InfinityCategories.Derived.Localization.SimplexAttachmentFamilies
public import SerrePositivity.InfinityCategories.F1.Transport.PointFunctorEvaluation

/-!
概要：共通実分母上の次辺の全族を、同じ分母で精密化した前段へ貼る。
方針：終端分母の精密化と、共有始点を保つ実 attachment の全族の延長を使う。
規約：次辺は元の実次辺の族そのもの。パラメータの有限性や新たな整合仮定は不要。
使われ方：完成分数の相対回収から第一行単体の比較へ進む実図式側の接続。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalClosed SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories SerrePositivity.KST.Fibration
namespace SerrePositivity.KST.LocalizingInvariants
end SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.InfinityCategories.Derived.Verdier.Fractions
open SerrePositivity.KST.LocalizingInvariants

/-- 共通実分母の次辺族を、精密化した同じ前段へ全パラメータで厳密に貼る。 -/
lemma exists_verdierSimplexCommonDenominatorFamily
    {A B C : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.StableCategory.{u}} {i : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap A B} {q : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap B C}
    (h : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.IsVerdierSequence i q) {n : ℕ} (D : (Δ[n] : SSet.{u}) ⟶ B.obj)
    (z : B.obj _⦋0⦌)
    (d : (verdierDenominatorOver i
      (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))) : SSet.{u}) _⦋0⦌)
    {K : SSet.{u}}
    (g : K ⟶ vertexFiber (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierDenominatorSpanProjection i
      (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))) z) d) :
    ∃ (D' : (Δ[n] : SSet.{u}) ⟶ B.obj)
      (t : Truncated.Edge (X := (truncation 2).obj ((ihom (Δ[n] : SSet.{u})).obj B.obj))
        (functorVertex D') (functorVertex D))
      (F : K ⟶ (ihom (join (Δ[n] : SSet.{u}) Δ[0])).obj B.obj),
      t.edge ∈ (relativeFirstRowSimplex q n).obj (Opposite.op ⦋1⦌) ∧
      D'.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n)) =
        (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierDenominatorOverSource i
          (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n)))).app
            (Opposite.op ⦋0⦌) d ∧
      (evaluateFunctorAt (Y := B.obj) (stdSimplex.obj₀Equiv.symm (Fin.last n))).app
        (Opposite.op ⦋1⦌) t.edge =
        (roofPointSliceVertexEdge (SSet.yonedaEquiv.symm
          (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n)))) d.val).edge ∧
      F ≫ (pre (joinInl (Δ[n] : SSet.{u}) Δ[0])).app B.obj =
        SSet.const (functorVertex D') ∧
      F ≫ (pre (joinMap (_root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.simplexLastPoint n) (𝟙 Δ[0]))).app B.obj =
        g ≫ _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierDenominatorSpanFiberArrow i
          (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))) z d ≫
          (pre (joinStdSimplexIso 0 0).hom).app B.obj := by
  let x := D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))
  let s := roofPointSliceVertexEdge (SSet.yonedaEquiv.symm x) d.val
  let s' := (SSet.Edge.ofTruncated (X := B.obj) s).ofEq rfl
    (Equiv.apply_symm_apply SSet.yonedaEquiv x)
  have hs : s'.edge ∈ _root_.SerrePositivity.InfinityCategories.Stable.Verdier.Fractions.weakEquivalences i := fullSubcomplexOnVertices_vertex d
  obtain ⟨D', t, ht, hv, hlast⟩ :=
    exists_verdierSimplexTerminalRefinementMap h D s'.toTruncated hs
  let a : K ⟶ (ihom (Δ[n] : SSet.{u})).obj B.obj := SSet.const (functorVertex D')
  let b := g ≫ _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierDenominatorSpanFiberArrow i x z d ≫
    (pre (joinStdSimplexIso 0 0).hom).app B.obj
  have ha : a ≫ (pre (_root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.simplexLastPoint n)).app B.obj ≫
      (pointFunctorEvaluationIso B.obj).hom =
      SSet.const ((_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierDenominatorOverSource i x).app (Opposite.op ⦋0⦌) d) := by
    change SSet.const (functorVertex D') ≫ (pre (_root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.simplexLastPoint n)).app B.obj ≫
      evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 1)) = _
    rw [stable_pre_evaluateFunctorAt, SSet.const_comp,
      evaluateFunctorAt_functorVertex]
    have hp : (_root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.simplexLastPoint n).app (Opposite.op ⦋0⦌)
        (stdSimplex.obj₀Equiv.symm (0 : Fin 1)) = stdSimplex.obj₀Equiv.symm (Fin.last n) := by
      have hp : stdSimplex.obj₀Equiv.symm (0 : Fin 1) =
          SSet.yonedaEquiv (𝟙 (Δ[0] : SSet.{u})) := by decide
      rw [hp, ← SSet.yonedaEquiv_comp, Category.id_comp]
      exact Equiv.apply_symm_apply _ _
    rw [hp, hv]
    rfl
  have hb : b ≫ (pre (joinInl (Δ[0] : SSet.{u}) Δ[0])).app B.obj ≫
      (pointFunctorEvaluationIso B.obj).hom =
      SSet.const ((_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierDenominatorOverSource i x).app (Opposite.op ⦋0⦌) d) := by
    change g ≫ _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierDenominatorSpanFiberArrow i x z d ≫
      (pre (joinStdSimplexIso 0 0).hom).app B.obj ≫
      (pre (joinInl (Δ[0] : SSet.{u}) Δ[0])).app B.obj ≫
      evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 1)) = _
    rw [stable_pre_evaluateFunctorAt, stable_pre_evaluateFunctorAt]
    change g ≫ _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierDenominatorSpanFiberArrow i x z d ≫
      evaluateFunctorAt (Y := B.obj) (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) = _
    rw [_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierDenominatorSpanFiberArrow_source, SSet.comp_const]
  have hab : a ≫ (pre (_root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.simplexLastPoint n)).app B.obj =
      b ≫ (pre (joinInl (Δ[0] : SSet.{u}) Δ[0])).app B.obj := by
    apply (cancel_mono (pointFunctorEvaluationIso B.obj).hom).mp
    simpa only [Category.assoc] using ha.trans hb.symm
  let T := _root_.SerrePositivity.InfinityCategories.Derived.Localization.simplexAttachmentFamilyGlue n a b hab
  let p := (pre (_root_.SerrePositivity.InfinityCategories.Derived.Localization.simplexAttachmentBoundary n).ι).app B.obj
  obtain ⟨r, hr⟩ := trivialKanFibration_exists_section p
  let F := T ≫ r
  have hF : F ≫ p = T := by rw [Category.assoc, hr, Category.comp_id]
  refine ⟨D', t, F, ht, hv, hlast, ?_, ?_⟩
  · have he := congrArg (fun f => f ≫ (pre (_root_.SerrePositivity.InfinityCategories.Derived.Localization.simplexAttachmentPrefix n)).app B.obj) hF
    simpa only [p, T, Category.assoc, ← NatTrans.comp_app, ← pre_map,
      _root_.SerrePositivity.InfinityCategories.Derived.Localization.simplexAttachmentPrefix_ι, _root_.SerrePositivity.InfinityCategories.Derived.Localization.simplexAttachmentFamilyGlue_prefix] using he
  · have he := congrArg (fun f => f ≫ (pre (_root_.SerrePositivity.InfinityCategories.Derived.Localization.simplexAttachmentLastEdge n)).app B.obj) hF
    simpa only [p, T, Category.assoc, ← NatTrans.comp_app, ← pre_map,
      _root_.SerrePositivity.InfinityCategories.Derived.Localization.simplexAttachmentLastEdge_ι, _root_.SerrePositivity.InfinityCategories.Derived.Localization.simplexAttachmentFamilyGlue_lastEdge] using he

end SerrePositivity.InfinityCategories.Derived.Verdier.Fractions

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.exists_verdierSimplexCommonDenominatorFamily := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.exists_verdierSimplexCommonDenominatorFamily
