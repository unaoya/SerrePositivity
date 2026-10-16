module
public import SerrePositivity.DifferentialGraded.Complexes.TensorZeroCochainLaws

/-! # 次数0 cochainのtensor評価と結合的作用の持ち上げ -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable {A : Type u} [CommRing A]

lemma tensorZeroCochain_postcomp_left {P P' Q Q' T : Complex A}
    (f : Cochain P P' 0) (g : Cochain Q Q' 0) (c : P' ⟶ T) :
    tensorZeroCochain (f.comp (Cochain.ofHom c) (zero_add 0)) g =
      (tensorZeroCochain f g).comp (Cochain.ofHom (c ▷ Q')) (zero_add 0) := by
  simpa only [tensorZeroCochain_ofHom, tensorHom_id, Cochain.comp_id] using
    (tensorZeroCochain_comp f g (Cochain.ofHom c) (Cochain.ofHom (𝟙 Q'))).symm

lemma tensorZeroCochain_postcomp_right {P P' Q Q' T : Complex A}
    (f : Cochain P P' 0) (g : Cochain Q Q' 0) (c : Q' ⟶ T) :
    tensorZeroCochain f (g.comp (Cochain.ofHom c) (zero_add 0)) =
      (tensorZeroCochain f g).comp (Cochain.ofHom (P' ◁ c)) (zero_add 0) := by
  simpa only [tensorZeroCochain_ofHom, id_tensorHom, Cochain.comp_id] using
    (tensorZeroCochain_comp f g (Cochain.ofHom (𝟙 P')) (Cochain.ofHom c)).symm

lemma tensorZeroCochain_precomp {P P' P'' Q Q' Q'' : Complex A}
    (c : P ⟶ P') (d : Q ⟶ Q') (f : Cochain P' P'' 0) (g : Cochain Q' Q'' 0) :
    (Cochain.ofHom (c ⊗ₘ d)).comp (tensorZeroCochain f g) (zero_add 0) =
      tensorZeroCochain ((Cochain.ofHom c).comp f (zero_add 0))
        ((Cochain.ofHom d).comp g (zero_add 0)) := by
  simpa only [tensorZeroCochain_ofHom] using
    tensorZeroCochain_comp (Cochain.ofHom c) (Cochain.ofHom d) f g

lemma tensorZeroCochain_multiply_assoc {P P' Q Q' R R' U V W : Complex A}
    (f : Cochain P P' 0) (g : Cochain Q Q' 0) (h : Cochain R R' 0)
    (c : P' ⊗ Q' ⟶ U) (d : U ⊗ R' ⟶ W) (e : Q' ⊗ R' ⟶ V) (k : P' ⊗ V ⟶ W)
    (ha : (c ▷ R') ≫ d = (α_ P' Q' R').hom ≫ P' ◁ e ≫ k) :
    (tensorZeroCochain ((tensorZeroCochain f g).comp (Cochain.ofHom c) (zero_add 0)) h).comp
      (Cochain.ofHom d) (zero_add 0) =
    (Cochain.ofHom (α_ P Q R).hom).comp
      ((tensorZeroCochain f ((tensorZeroCochain g h).comp (Cochain.ofHom e) (zero_add 0))).comp
        (Cochain.ofHom k) (zero_add 0)) (zero_add 0) := by
  have hh := congrArg (fun t : Cochain ((P ⊗ Q) ⊗ R) (P' ⊗ (Q' ⊗ R')) 0 =>
    t.comp (Cochain.ofHom (P' ◁ e ≫ k)) (zero_add 0)) (tensorZeroCochain_assoc f g h)
  rw [tensorZeroCochain_postcomp_left, tensorZeroCochain_postcomp_right]
  simp only [Cochain.comp_assoc_of_first_is_zero_cochain]
  rw [← Cochain.ofHom_comp, ha]
  simpa only [Cochain.ofHom_comp, Cochain.comp_assoc_of_first_is_zero_cochain] using hh

lemma tensorCarry_evaluation {K K' P P' Q Q' T T' U V : Complex A}
    (r : Cochain K K' 0) (a : Cochain P P' 0) (b : Cochain Q Q' 0) (c : Cochain T T' 0)
    (m : P ⊗ Q ⟶ T) (n : P' ⊗ Q' ⟶ T')
    (e : K' ⊗ P' ⟶ U) (e' : K' ⊗ T' ⟶ V) (n' : U ⊗ Q' ⟶ V)
    (hm : (Cochain.ofHom m).comp c (zero_add 0) =
      (tensorZeroCochain a b).comp (Cochain.ofHom n) (zero_add 0))
    (ha : (e ▷ Q') ≫ n' = (α_ K' P' Q').hom ≫ K' ◁ n ≫ e') :
    (Cochain.ofHom ((α_ K P Q).hom ≫ K ◁ m)).comp
      ((tensorZeroCochain r c).comp (Cochain.ofHom e') (zero_add 0)) (zero_add 0) =
    (tensorZeroCochain ((tensorZeroCochain r a).comp (Cochain.ofHom e) (zero_add 0)) b).comp
      (Cochain.ofHom n') (zero_add 0) := by
  have hc : (Cochain.ofHom (K ◁ m)).comp (tensorZeroCochain r c) (zero_add 0) =
      tensorZeroCochain r ((Cochain.ofHom m).comp c (zero_add 0)) := by
    simpa only [id_tensorHom, Cochain.id_comp] using
      tensorZeroCochain_precomp (𝟙 K) m r c
  have hp := congrArg (fun z : Cochain (K ⊗ (P ⊗ Q)) (K' ⊗ T') 0 =>
    (Cochain.ofHom (α_ K P Q).hom).comp
      (z.comp (Cochain.ofHom e') (zero_add 0)) (zero_add 0)) hc
  calc
    _ = (Cochain.ofHom (α_ K P Q).hom).comp
        ((tensorZeroCochain r ((Cochain.ofHom m).comp c (zero_add 0))).comp
          (Cochain.ofHom e') (zero_add 0)) (zero_add 0) := by
      simpa only [Cochain.ofHom_comp, Cochain.comp_assoc_of_first_is_zero_cochain] using hp
    _ = _ := by
      rw [hm]
      exact (tensorZeroCochain_multiply_assoc r a b e n' n e' ha).symm

end SerrePositivity.DifferentialGraded
