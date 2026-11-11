module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.BasedCoefficientAction
/-!
概要：始点支持のある全係数の押出しは、始点保存ラベルへの制限と交換する。
方針：制限を部分型からの延長で戻し、二つの有限支持押出しを関数合成で同定する。
規約：始点支持を明示仮定とし、任意の全係数についての自然性は主張しない。
使われ方：Hσ の係数自然性と実 Hom の係数押出しを接続する。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract
open CategoryTheory SSet
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R]

lemma dgCoherentBarBasedCoefficients_extend {m n : ℕ}
    (z : ((Δ[m] : SSet.{u}) _⦋n⦌) →₀ R)
    (hz : ∀ a ∈ z.support, a 0 = 0) :
    Finsupp.mapDomain Subtype.val (z.subtypeDomain (fun a => a 0 = 0)) = z := by
  calc
    _ = Finsupp.embDomain
        (Function.Embedding.subtype (fun a : (Δ[m] : SSet.{u}) _⦋n⦌ => a 0 = 0))
        (z.subtypeDomain (fun a => a 0 = 0)) :=
      (Finsupp.embDomain_eq_mapDomain _ _).symm
    _ = (z.subtypeDomain (fun a => a 0 = 0)).extendDomain :=
      (Finsupp.extendDomain_eq_embDomain_subtype _).symm
    _ = z := Finsupp.extendDomain_subtypeDomain z hz

lemma dgCoherentBarBasedCoefficients_restrict_extend {m n : ℕ}
    (z : _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.DGCoherentBarBasedLabel.{u} m n →₀ R) :
    (Finsupp.mapDomain Subtype.val z).subtypeDomain (fun a => a 0 = 0) = z := by
  have h : Finsupp.mapDomain Subtype.val z = z.extendDomain :=
    (Finsupp.embDomain_eq_mapDomain (Function.Embedding.subtype
      (fun a : (Δ[m] : SSet.{u}) _⦋n⦌ => a 0 = 0)) z).symm.trans
      (Finsupp.extendDomain_eq_embDomain_subtype z).symm
  rw [h]
  exact Finsupp.subtypeDomain_extendDomain z

lemma dgCoherentBarBasedCoefficients_push {l m n : ℕ}
    (f : ⦋m⦌ ⟶ ⦋l⦌) (hf : f.toOrderHom 0 = 0)
    (z : ((Δ[m] : SSet.{u}) _⦋n⦌) →₀ R)
    (hz : ∀ a ∈ z.support, a 0 = 0) :
    (Finsupp.mapDomain ((SSet.stdSimplex.map f).app (Opposite.op ⦋n⦌)) z).subtypeDomain
        (fun a => a 0 = 0) =
      Finsupp.mapDomain (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.dgCoherentBarBasedLabelPush f hf)
        (z.subtypeDomain (fun a => a 0 = 0)) := by
  have hext := dgCoherentBarBasedCoefficients_extend R z hz
  have hfun :
      ((SSet.stdSimplex.map f).app (Opposite.op ⦋n⦌)) ∘
        (Subtype.val : _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.DGCoherentBarBasedLabel.{u} m n → (Δ[m] : SSet.{u}) _⦋n⦌) =
      (Subtype.val : _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.DGCoherentBarBasedLabel.{u} l n → (Δ[l] : SSet.{u}) _⦋n⦌) ∘
        _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.dgCoherentBarBasedLabelPush f hf := rfl
  calc
    _ = (Finsupp.mapDomain ((SSet.stdSimplex.map f).app (Opposite.op ⦋n⦌))
        (Finsupp.mapDomain Subtype.val (z.subtypeDomain (fun a => a 0 = 0)))).subtypeDomain
          (fun a => a 0 = 0) := congrArg (fun t =>
            (Finsupp.mapDomain ((SSet.stdSimplex.map f).app (Opposite.op ⦋n⦌)) t).subtypeDomain
              (fun a => a 0 = 0)) hext.symm
    _ = (Finsupp.mapDomain Subtype.val
        (Finsupp.mapDomain (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract.dgCoherentBarBasedLabelPush f hf)
          (z.subtypeDomain (fun a => a 0 = 0)))).subtypeDomain (fun a => a 0 = 0) := by
      rw [← Finsupp.mapDomain_comp, hfun, Finsupp.mapDomain_comp]
    _ = _ := dgCoherentBarBasedCoefficients_restrict_extend R _

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Retract
