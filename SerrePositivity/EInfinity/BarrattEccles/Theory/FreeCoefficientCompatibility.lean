module

public import SerrePositivity.EInfinity.BarrattEccles.Theory.FreeStandardCoefficients

/-!
# 自由 Schur 比較と指定係数射の照合

HA 3.2.4.7。指定商写像と Schur の生成射を前合成し、構成した同値の順射を照合する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory Limits MonoidalCategory HomologicalComplex
open SerrePositivity.DifferentialGraded SerrePositivity.TensorPowers
variable (R : Type u) [CommRing R] (X Y : Complex R) (m n : ℕ)

/-- テンソル側の表示同型は、左右の元の生成射を同じ arity の指定商へ送る。 -/
lemma schurTensorArityIso_generators :
    (schurι R (sequence R) X m ⊗ₘ schurι R (sequence R) Y n) ≫
      (schurTensorArityIso X Y).hom =
    (arityCoinvariantComplexQuotient (schurDiagram R (sequence R) X) m ⊗ₘ
      arityCoinvariantComplexQuotient (schurDiagram R (sequence R) Y) n) ≫
        Sigma.ι (fun p : ℕ × ℕ =>
          arityCoinvariantComplex (schurDiagram R (sequence R) X) p.1 ⊗
          arityCoinvariantComplex (schurDiagram R (sequence R) Y) p.2) (m, n) := by
  simp only [schurTensorArityIso, Iso.trans_hom, tensorIso_hom, tensorCoproductPairIso, schurι]
  rw [tensorHom_comp_tensorHom_assoc]
  simp only [schurComplexArityIso, arityCoinvariantComplexIso_ι]
  rw [← tensorHom_comp_tensorHom_assoc, tensorCoproductDesc_ι]

/-- 実際の arity の商を入力優先の表示へ送ると、同じテンソル余不変の商となる。 -/
lemma schurArityInputCoefficientIso_quotient (K : Complex R) (r : ℕ) :
    arityCoinvariantComplexQuotient (schurDiagram R (sequence R) K) r ≫
      (schurArityInputCoefficientIso R K r).hom =
    (β_ ((operad R).arity r) (SerrePositivity.TensorPowers.power K r)).hom ≫
      coinvariantTotalQuotient
        (finiteBijectionComplexAction (bijectionFunctor K) r) (arityComplexAction R r) := by
  let ρ := finiteBijectionComplexAction (bijectionFunctor K) r
  let σ := finiteBijectionComplexAction (sequence R) r
  let d := finiteBijectionComplexAction (schurDiagram R (sequence R) K) r
  let F :=
    (forget₂ (Rep.{u} R (ULift.{u} (Equiv.Perm (Fin r)))) (ModuleCat R)).mapHomologicalComplex
      (.up ℤ)
  let Q := NatTrans.mapHomologicalComplex
    (Rep.coinvariantsMk R (ULift.{u} (Equiv.Perm (Fin r)))) (.up ℤ)
  let e := eqToIso (congrArg representationCochainComplex
    (schurDiagramComplexAction (sequence R) K r)) ≪≫ representationTensorBraidingIso σ ρ
  have ht {L : Complex R} (a b : ULift.{u} (Equiv.Perm (Fin r)) →* End L)
      (h : a = b) : (representationCochainForgetIso a).inv ≫
        F.map (eqToIso (congrArg representationCochainComplex h)).hom =
          (representationCochainForgetIso b).inv := by
    subst b
    simp [F]
  have he : (representationCochainForgetIso d).inv ≫ F.map e.hom =
      (β_ ((operad R).arity r) (power K r)).hom ≫
        (representationCochainForgetIso (tensorComplexAction ρ σ)).inv := by
    dsimp only [e]
    rw [Iso.trans_hom, Functor.map_comp, ← Category.assoc,
      ht d (tensorComplexAction σ ρ) (schurDiagramComplexAction (sequence R) K r)]
    apply HomologicalComplex.Hom.ext
    funext i
    apply ModuleCat.hom_ext
    rfl
  have hn := congrArg (fun q => (representationCochainForgetIso d).inv ≫ q)
    (Q.naturality e.hom).symm
  have hh := congrArg (fun q => q ≫ Q.app
    (representationCochainComplex (tensorComplexAction ρ σ))) he
  have hb := hn.trans (by simpa only [Category.assoc] using hh)
  have hi : arityCoinvariantComplexQuotient (schurDiagram R (sequence R) K) r ≫
      (schurArityTotalIso (sequence R) K r).hom ≫
        (coinvariantTensorTotalSwapIso σ ρ).hom =
      (β_ ((operad R).arity r) (power K r)).hom ≫ coinvariantTotalQuotient ρ σ := by
    apply (cancel_mono (coinvariantTensorTotalIso ρ σ).hom).1
    simpa only [arityCoinvariantComplexQuotient, schurArityTotalIso,
      coinvariantTensorTotalSwapIso, coinvariantTotalQuotient, Iso.trans_hom, Iso.symm_hom,
      Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id,
      Functor.mapIso_hom, Functor.map_comp, e, σ, ρ, d, Q] using hb
  trans (β_ ((operad R).arity r) (power K r)).hom ≫ coinvariantTotalQuotient ρ σ ≫
    (((Rep.coinvariantsTensor R (ULift.{u} (Equiv.Perm (Fin r)))).map₂CochainComplex.obj
      (representationCochainComplex ρ)).mapIso (sequenceArityRepresentationIso R r)).hom
  · simpa only [schurArityInputCoefficientIso, Iso.trans_hom, Category.assoc] using
      congrArg (fun q => q ≫
        (((Rep.coinvariantsTensor R (ULift.{u} (Equiv.Perm (Fin r)))).map₂CochainComplex.obj
          (representationCochainComplex ρ)).mapIso (sequenceArityRepresentationIso R r)).hom) hi
  · have ht (s t : ULift.{u} (Equiv.Perm (Fin r)) →* End ((operad R).arity r))
        (h : s = t) : coinvariantTotalQuotient ρ s ≫
          (((Rep.coinvariantsTensor R (ULift.{u} (Equiv.Perm (Fin r)))).map₂CochainComplex.obj
            (representationCochainComplex ρ)).mapIso
              (eqToIso (congrArg representationCochainComplex h))).hom =
                coinvariantTotalQuotient ρ t := by
      subst t
      simp only [Functor.mapIso_hom, eqToIso.hom, eqToHom_refl]
      let T := ((Rep.coinvariantsTensor R (ULift.{u} (Equiv.Perm (Fin r)))).map₂CochainComplex).obj
        (representationCochainComplex ρ)
      exact (congrArg (fun q => coinvariantTotalQuotient ρ s ≫ q)
        (T.map_id (representationCochainComplex s))).trans
          (Category.comp_id (coinvariantTotalQuotient ρ s))
    exact congrArg (fun q => (β_ ((operad R).arity r) (power K r)).hom ≫ q)
      (ht σ (arityComplexAction R r) (sequenceComplexAction_eq R r))

end SerrePositivity.EInfinity.BarrattEccles
