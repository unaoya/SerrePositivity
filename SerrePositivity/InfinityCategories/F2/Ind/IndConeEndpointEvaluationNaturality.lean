module

public import SerrePositivity.InfinityCategories.F2.CatInfinity.FunctorIsoTransportAlgebra
public import SerrePositivity.InfinityCategories.F2.Ind.IndConeEndpointEvaluationComparison
public import SerrePositivity.InfinityCategories.F2.Ind.IndConeEndpointRawFaceIsoNaturality

/-!
概要：同じ初期全円柱を保持する再構成では、元の極大点評価への旧族比較の指定値は不変。
方針：同じ実 comma の指定比較を元の点表示同型で移し、元の評価へ厳密に戻す。
規約：元の全評価と指定同型の値を保持する。
使われ方：指定変換を元の旧族で保持したまま、終点拡張を選び直す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
variable {κ : Cardinal.{u}} {L C : SSet.{u}} [Quasicategory C]
  {D : (SSet.uliftFunctor.{u + 1, u}).obj (join L (Δ[0] : SSet.{u})) ⟶ IndInfinity κ C}
  {T : SSet.{u + 1}} {q : T ⟶ diagramComma κ D}
  {G : JoinCocone (q ≫ diagramCommaRestriction κ D (joinInl L (Δ[0] : SSet.{u})))}
  (V : IndConeExtendedSliceData κ D q G)
/-- 概要：元の極大点評価へ表示を戻しても、同じ実終点族の指定比較の値を保持する。
方針：元の端点の等号だけで移送。規約：同じ指定値。使われ方：旧族での比較の回収。 -/
lemma indConeEndpointEvaluationIso_heq :
    HEq (indConeEndpointEvaluationIso V) (indConeEndpointFaceIso V) :=
  F2.functorIsoOfEq_heq _ _ _
/-- 概要：元の評価への表示変更後も、任意の制限で同じ指定比較の値を保持する。
方針：元の同型と端点の等号の自然性。規約：指定値を保持。使われ方：旧族の変換保持。 -/
lemma indConeEndpointEvaluationIso_precomp_heq {A₀ : SSet.{u + 1}}
    (i : A₀ ⟶ join T (Δ[0] : SSet.{u + 1})) : HEq
    ((indConeEndpointEvaluationIso V).precomp i) ((indConeEndpointFaceIso V).precomp i) :=
  F2.functorIso_precomp_heq_of_heq (indConeEndpointFaceIso V) (indConeEndpointEvaluationIso V)
    rfl (indConeEndpointEvaluation_eq_reconstructed V).symm (indConeEndpointEvaluationIso_heq V) i
/-- 概要：同じ初期全円柱を保持する再構成では、標準終点 comma の旧族比較の値は不変。
方針：元の実 comma の指定比較を同じ点表示同型で移す。規約：同じ指定値。
使われ方：元の極大点評価の比較の旧族回収。 -/
lemma indConeEndpointFaceIso_old_heq (V' : IndConeExtendedSliceData κ D q G)
    (hInitial : V.initial = V'.initial) : HEq
    ((indConeEndpointFaceIso V).precomp (joinInl T (Δ[0] : SSet.{u + 1})))
    ((indConeEndpointFaceIso V').precomp (joinInl T (Δ[0] : SSet.{u + 1}))) := by
  let i := joinInl T (Δ[0] : SSet.{u + 1})
  let e := (indConeEndpointCommaIso κ D).hom
  have h := F2.functorIso_postcomp_heq_of_heq
    ((indConeEndpointRawFaceIso V').precomp i) ((indConeEndpointRawFaceIso V).precomp i)
    (indConeEndpointRawFace_old_eq V V' hInitial).symm
    (indConeEndpointReconstructedRawFace_old_eq V V' hInitial).symm
    (indConeEndpointRawFaceIso_old_heq V V' hInitial) e
  exact (heq_of_eq (F2.functorIso_precomp_postcomp (indConeEndpointRawFaceIso V) i e).symm).trans
    (h.trans (heq_of_eq (F2.functorIso_precomp_postcomp (indConeEndpointRawFaceIso V') i e)))
/-- 概要：同じ初期全円柱を保持する再構成では、元の極大点評価への旧族比較の値は不変。
方針：実 comma の同じ比較の値と、元の評価の厳密な回収を合成する。
規約：元の指定評価と指定同型を保持。使われ方：指定変換を変えない相対余錐の構成。 -/
lemma indConeEndpointEvaluationIso_old_heq (V' : IndConeExtendedSliceData κ D q G)
    (hInitial : V.initial = V'.initial) : HEq
    ((indConeEndpointEvaluationIso V).precomp (joinInl T (Δ[0] : SSet.{u + 1})))
    ((indConeEndpointEvaluationIso V').precomp (joinInl T (Δ[0] : SSet.{u + 1}))) := by
  exact (indConeEndpointEvaluationIso_precomp_heq V _).trans
    ((indConeEndpointFaceIso_old_heq V V' hInitial).trans
      (indConeEndpointEvaluationIso_precomp_heq V' _).symm)
end SerrePositivity.InfinityCategories.F2.Ind
