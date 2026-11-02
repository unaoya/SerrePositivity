module

public import SerrePositivity.InfinityCategories.F2.Ind.FunctorIsoInverseHEq
public import SerrePositivity.InfinityCategories.Core.FilteredExchange.CoconeExistenceTransport

/-!
概要：全余錐の指定比較と旧族の指定下側比較が一致すると、元の実 under comma に余錐。
方針：下側 left fibration で全比較を持ち上げ、旧族で元の指定比較と逆を相殺する。
規約：元の上側族と元の指定変換を保持し、比較の存在だけでは結論しない。
使われ方：元の極大点評価下への相対拡張の帰還。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
/-- 概要：全比較の旧族値と指定下側比較が一致すれば、元の相対族に余錐がある。
方針：全指定比較を持ち上げて旧族の往復を相殺する。
規約：同じ q と指定 t を回収。使われ方：指定評価の共終性。 -/
lemma nonempty_relativeCommaFamily_cocone_of_comparison
    {A K E B : SSet.{u}} [Quasicategory E] [Quasicategory B]
    (e : E ⟶ B) (z : K ⟶ B) (q : A ⟶ E) (t : A ⟶ sliceUnder z)
    (ht : q ≫ e = t ≫ sliceUnderProjection z)
    (Q : join A (Δ[0] : SSet.{u}) ⟶ E) (hQ : joinInl A Δ[0] ≫ Q = q)
    (F : join A (Δ[0] : SSet.{u}) ⟶ B) (d : FunctorIso F (Q ≫ e))
    (u : A ⟶ sliceUnder z) (c : JoinCocone u) (hc : c.val ≫ sliceUnderProjection z = F)
    (L : FunctorIso u t)
    (hL : HEq (L.postcomp (sliceUnderProjection z)) (d.precomp (joinInl A Δ[0]))) :
    Nonempty (JoinCocone (relativeCommaFamily e z t q ht)) := by
  let p := sliceUnderProjection z
  let i := joinInl A (Δ[0] : SSet.{u})
  let d' := F2.functorIsoOfEq d.symm rfl hc.symm
  let s := pathCorrectedFunctorSquare p (leftFibration_equivalenceLifting p) c.val (Q ≫ e) d'
  let a := i ≫ s.map
  have ha : q ≫ e = a ≫ p := by
    dsimp only [a]
    rw [Category.assoc, s.comm, ← Category.assoc, hQ]
  let L₀ := F2.functorIsoOfEq (s.exactComponentIso.precomp i) rfl c.property
  have h₀ : HEq (L₀.postcomp p) ((d.precomp i).symm) := by
    have h := (functorIsoOfEq_postcomp_heq _ rfl c.property p).trans
      ((s.exactComponentIso_precomp_postcomp_heq i).trans
        (functorIsoOfEq_precomp_heq d.symm rfl hc.symm i))
    exact h.trans (heq_of_eq (F2.functorIso_precomp_symm d i))
  have hL₀ : a ≫ p = i ≫ (Q ≫ e) := by
    dsimp only [a]
    rw [Category.assoc, s.comm]
  have hL₁ : u ≫ p = i ≫ F := by
    rw [← hc, ← Category.assoc, c.property]
  have hL₂ : t ≫ p = i ≫ (Q ≫ e) := by
    rw [← ht, ← Category.assoc, hQ]
  let R : FunctorIso a t := L₀ ≪≫ L
  have hR : F2.IsFunctorEqIso (R.postcomp p) := by
    dsimp only [R]
    rw [F2.functorIso_postcomp_trans]
    exact isFunctorEqIso_trans_of_inverse_pair_heq _ _ (d.precomp i)
      hL₀ hL₁ hL₂ h₀ hL
  obtain ⟨r⟩ := nonempty_relativeCommaFamily_iso_of_lowerIso e z q a t ha ht R hR
  let U := relativeCommaFamily e z s.map Q s.comm.symm
  have hU : i ≫ U = relativeCommaFamily e z a q ha := by
    apply pullback.hom_ext
    · simp only [U, relativeCommaFamily, Category.assoc, pullback.lift_fst]
      rfl
    · simp only [U, relativeCommaFamily, Category.assoc, pullback.lift_snd]
      exact hQ
  exact nonempty_joinCocone_of_functorIso r ⟨⟨U, hU⟩⟩
end SerrePositivity.InfinityCategories.F2.Ind
