module

public import SerrePositivity.AlgebraicGeometry.GenericFreeReducedAlgebra
public import SerrePositivity.AlgebraicGeometry.GeometricallyIntegralCompletionBaseChange
public import SerrePositivity.AlgebraicGeometry.NilpotentProjectivity
public import Mathlib.RingTheory.Noetherian.Nilpotent

/-!
概要：Noether 環上の平坦有限型代数が幾何学的整なファイバーを持つときの射影性（Stacks 05FS）。
方針：基底のイデアルで Noether 帰納し、冪零剰余または局所化と完備化の判定を適用する。
規約：射影性は基底環上。代数が基底加群として有限であるとは仮定しない。
使われ方：平坦化で用いる、幾何学的整な平坦有限表示代数の自由加群への分裂。
-/

@[expose] public noncomputable section
universe u

namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry
open scoped TensorProduct

private theorem projective_tensor_of_baseEquiv
    {R C D B : Type u} [CommRing R] [CommRing C] [CommRing D] [CommRing B]
    [Algebra R C] [Algebra R D] [Algebra R B] (e : C ≃ₐ[R] D)
    (h : Module.Projective C (C ⊗[R] B)) : Module.Projective D (D ⊗[R] B) := by
  let : Module.Projective C (C ⊗[R] B) := h
  let := RingHomInvPair.of_ringEquiv e.toRingEquiv
  let := RingHomInvPair.of_ringEquiv e.toRingEquiv.symm
  exact Module.Projective.of_equiv (tensorBaseChangeSemilinearEquiv e)

private theorem projective_reduction_of_larger_ideal
    {R B : Type u} [CommRing R] [CommRing B] [Algebra R B]
    (I : Ideal R) (J : Ideal (R ⧸ I)) (hJ : J ≠ ⊥)
    (ih : ∀ K > I, Module.Projective (R ⧸ K) ((R ⧸ K) ⊗[R] B)) :
    Module.Projective ((R ⧸ I) ⧸ J)
      (((R ⧸ I) ⊗[R] B) ⧸ (J • (⊤ : Submodule (R ⧸ I) ((R ⧸ I) ⊗[R] B)))) := by
  let C := R ⧸ I
  let D := C ⧸ J
  let f : R →ₐ[R] D := Algebra.ofId R D
  have hf : Function.Surjective f :=
    Ideal.Quotient.mk_surjective.comp Ideal.Quotient.mk_surjective
  have hker : RingHom.ker f.toRingHom = J.comap (Ideal.Quotient.mk I) := by
    change RingHom.ker ((Ideal.Quotient.mk J).comp (Ideal.Quotient.mk I)) = _
    rw [← RingHom.comap_ker, Ideal.mk_ker]
  have hlt : I < RingHom.ker f.toRingHom := by
    rw [hker]
    calc
      I = (⊥ : Ideal C).comap (Ideal.Quotient.mk I) := (Ideal.mk_ker (I := I)).symm
      _ < J.comap (Ideal.Quotient.mk I) := lt_of_le_of_ne (Ideal.comap_mono bot_le) fun he =>
        hJ ((Ideal.comap_injective_of_surjective _ Ideal.Quotient.mk_surjective he).symm)
  let e : (R ⧸ RingHom.ker f.toRingHom) ≃ₐ[R] D :=
    Ideal.quotientKerAlgEquivOfSurjective hf
  let : Module.Projective D (D ⊗[R] B) := projective_tensor_of_baseEquiv e (ih _ hlt)
  exact Module.Projective.of_equiv'
    ((Algebra.TensorProduct.cancelBaseChange R C D D B).toLinearEquiv.symm.trans
      (quotientModuleTensorEquiv J (C ⊗[R] B)))

/--
概要：幾何学的整なファイバーを持つ Noether 環上の平坦有限型代数は、基底上射影的。
方針：各商環への基底変更の射影性を Noether 帰納で示す。被約商では一般自由性と
局所化・完備化の判定を使い、非被約商では冪零イデアルを法とする射影性から持ち上げる。
規約：幾何学的整性は Spec の射の標準条件。Stacks 05FS の affine 版。
使われ方：平坦化のための射影代数からの自由化中心。
-/
theorem projective_of_flat_finiteType_geometricallyIntegral
    (R B : Type u) [CommRing R] [IsNoetherianRing R] [CommRing B] [Algebra R B]
    [Module.Flat R B] [Algebra.FiniteType R B]
    [GeometricallyIntegral (Spec.map (CommRingCat.ofHom (algebraMap R B)))] :
    Module.Projective R B := by
  have hall (I : Ideal R) : Module.Projective (R ⧸ I) ((R ⧸ I) ⊗[R] B) := by
    refine IsNoetherian.induction
      (P := fun J : Ideal R => Module.Projective (R ⧸ J) ((R ⧸ J) ⊗[R] B)) ?_ I
    intro I ih
    let C := R ⧸ I
    let A := C ⊗[R] B
    change Module.Projective C A
    rcases subsingleton_or_nontrivial C with hC | hC
    · let : Subsingleton C := hC
      let : Module.Free C A := Module.Free.of_subsingleton' C A
      infer_instance
    let : Nontrivial C := hC
    by_cases hred : IsReduced C
    · let : IsReduced C := hred
      obtain ⟨f, hf, hfree⟩ := exists_nonzero_free_localization_of_finiteType_of_isReduced C A
      let J := Ideal.span {f}
      have hJ : J ≠ ⊥ := by
        intro he
        have hm : f ∈ J := Ideal.subset_span (Set.mem_singleton f)
        rw [he, Ideal.mem_bot] at hm
        exact hf hm
      let : Module.Projective (C ⧸ J) (A ⧸ (J • (⊤ : Submodule C A))) :=
        projective_reduction_of_larger_ideal I J hJ ih
      let : Module.Free (Localization.Away f) (Localization.Away f ⊗[C] A) := hfree
      let : Algebra.FinitePresentation C A := Algebra.FinitePresentation.of_finiteType.mp
        inferInstance
      let : GeometricallyIntegral (Spec.map (CommRingCat.ofHom (algebraMap C A))) :=
        geometricallyIntegral_tensorProjection R B C
      exact projective_geometricallyIntegral_of_free_localization_of_projective_reduction C A f
    · let J := nilradical C
      have hJ : J ≠ ⊥ := fun he => hred (nilradical_eq_bot_iff.mp he)
      let : Module.Projective (C ⧸ J) (A ⧸ (J • (⊤ : Submodule C A))) :=
        projective_reduction_of_larger_ideal I J hJ ih
      obtain ⟨n, hn⟩ := IsNoetherianRing.isNilpotent_nilradical C
      exact projective_of_flat_of_projective_nilpotent_reduction J n hn
  let : Module.Projective R (R ⊗[R] B) :=
    projective_tensor_of_baseEquiv (AlgEquiv.quotientBot R R) (hall ⊥)
  exact Module.Projective.of_equiv' (Algebra.TensorProduct.lid R B).toLinearEquiv

end SerrePositivity.AlgebraicGeometry
