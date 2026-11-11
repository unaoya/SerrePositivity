module

public import SerrePositivity.AlgebraicGeometry.RelativeNoetherIntegralFibers

/-!
概要：相対 Noether 正規化の étale 局所模型を、平坦化の帰納で使う環準同型で表す。
方針：三つのアフィンスキームを大域切断環の Spec に置き換える。
規約：元のファイバー環の Krull 次元上限を入力する。
使われ方：Stacks 0815 で有限押し出しと基底側の中心降下を行う。
-/

@[expose] public noncomputable section

namespace SerrePositivity.AlgebraicGeometry

open _root_.AlgebraicGeometry CategoryTheory
open scoped TensorProduct

set_option backward.isDefEq.respectTransparency false in
/--
概要：有限型アフィン射の各点で、次元を抑えた滑らかで幾何学的整な族への有限な étale 局所模型を環で選べる。
方針：指定点の剰余体ファイバーの点から局所模型を取り、アフィン同型で写像を共役する。
規約：基底側と始域側の étale 写像の四角形は環準同型の合成式として返す。
使われ方：零化イデアルで切り出した台の全点を、有限個の平坦化可能な局所模型で覆う。
-/
theorem exists_affine_ring_normalization_at
    (R B : CommRingCat.{u}) [Algebra R B] [IsNoetherianRing R] [Algebra.FiniteType R B]
    (q : PrimeSpectrum B) (d : WithBot ℕ∞)
    (hd : ∀ p : PrimeSpectrum R, ringKrullDim (p.asIdeal.Fiber B) ≤ d) :
    ∃ (n : ℕ) (_ : (n : WithBot ℕ∞) ≤ d) (C E D : CommRingCat.{u})
      (e : R ⟶ C) (f : C ⟶ E) (h : E ⟶ D) (j : B ⟶ D) (q' : PrimeSpectrum D),
      e.hom.Etale ∧ j.hom.Etale ∧ h.hom.Finite ∧
      SmoothOfRelativeDimension n (Spec.map f) ∧ GeometricallyIntegral (Spec.map f) ∧
      q'.comap j.hom = q ∧
      e ≫ f ≫ h = CommRingCat.ofHom (algebraMap R B) ≫ j := by
  let p := q.comap (algebraMap R B)
  let iso := PrimeSpectrum.preimageHomeomorphFiber R B p
  let z := iso ⟨q, rfl⟩
  have hz : z.comap (Algebra.TensorProduct.includeRight : B →ₐ[R] p.asIdeal.Fiber B).toRingHom = q :=
    congrArg Subtype.val (iso.symm_apply_apply ⟨q, rfl⟩)
  obtain ⟨n, hn, S', Y', X', _, _, _, e, j, f, h, x, he, hj, hx, hcomm, hfin, hsm, hgi⟩ :=
    exists_dim_le_etale_finite_geometricallyIntegral_refinement p z d
      (fun _ _ _ => (ringKrullDim_le_of_surjective _ Ideal.Quotient.mk_surjective).trans (hd p))
  let e' := S'.isoSpec.inv ≫ e
  let j' := X'.isoSpec.inv ≫ j
  let f' := Y'.isoSpec.inv ≫ f ≫ S'.isoSpec.hom
  let h' := X'.isoSpec.inv ≫ h ≫ Y'.isoSpec.hom
  let φ := Spec.preimage e'
  let ψ := Spec.preimage f'
  let θ := Spec.preimage h'
  let κ := Spec.preimage j'
  have hφ : Spec.map φ = e' := Spec.map_preimage e'
  have hψ : Spec.map ψ = f' := Spec.map_preimage f'
  have hθ : Spec.map θ = h' := Spec.map_preimage h'
  have hκ : Spec.map κ = j' := Spec.map_preimage j'
  let x' := X'.isoSpec.hom x
  refine ⟨n, hn, _, _, _, φ, ψ, θ, κ, x', ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply (HasRingHomProperty.Spec_iff (P := @Etale)).mp
    rw [hφ]
    infer_instance
  · apply (HasRingHomProperty.Spec_iff (P := @Etale)).mp
    rw [hκ]
    infer_instance
  · apply (IsFinite.SpecMap_iff θ).mp
    rw [hθ]
    infer_instance
  · rw [hψ]
    exact (MorphismProperty.cancel_left_of_respectsIso (@SmoothOfRelativeDimension n) _ _).mpr
      ((MorphismProperty.cancel_right_of_respectsIso (@SmoothOfRelativeDimension n) f _).mpr hsm)
  · let : MorphismProperty.RespectsIso @GeometricallyIntegral := by
      rw [GeometricallyIntegral.eq_geometrically]
      infer_instance
    rw [hψ]
    exact (MorphismProperty.cancel_left_of_respectsIso @GeometricallyIntegral _ _).mpr
      ((MorphismProperty.cancel_right_of_respectsIso @GeometricallyIntegral f _).mpr hgi)
  · change Spec.map κ x' = q
    rw [hκ, show j' x' = j x by
      change (X'.isoSpec.hom ≫ X'.isoSpec.inv ≫ j) x = j x
      rw [Iso.hom_inv_id_assoc], hx, hz]
  · apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_comp, Spec.map_comp, hφ, hψ, hθ, hκ]
    simp only [e', j', f', h', Category.assoc, Iso.hom_inv_id_assoc]
    rw [hcomm]

end SerrePositivity.AlgebraicGeometry
