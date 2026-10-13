module

public import SerrePositivity.CommutativeAlgebra.ResidueFieldExtensionConstruction
public import Mathlib.Algebra.Polynomial.Lifts
public import Mathlib.RingTheory.Adjoin.PowerBasis
public import SerrePositivity.CommutativeAlgebra.ResidueFieldCompletion

/-! # 代数的単生成剰余体拡大の持ち上げ

指定体の冪基底の最小多項式を、次数を保ったモニック多項式へ持ち上げる。
その多項式の商を具体的な有限自由局所拡大とし、閉ファイバーと指定体の
同型を構成する。係数写像・生成元・剰余体写像を同じ同型で比較する。
有限自由な局所拡大には分離性・Noether性を使わず、純非分離の単生成拡大にも適用する。
基底環がNoetherなら、さらに完備化して完備Noether平坦局所拡大を得る。
-/

public section

universe u
namespace SerrePositivity
open IsLocalRing Polynomial

/-- 剰余体上のモニック多項式は、同じ次数のモニック多項式へ持ち上がる。 -/
theorem exists_monic_residue_lift {B : Type*} [CommRing B] [IsLocalRing B]
    (f : Polynomial (ResidueField B)) (hf : f.Monic) :
    ∃ F : Polynomial B, F.map (residue B) = f ∧ F.degree = f.degree ∧ F.Monic :=
  Polynomial.lifts_and_degree_eq_and_monic
    (Polynomial.mem_lifts_of_surjective (residue_surjective (R := B)) f) hf

section ClosedFibre
variable {B K : Type*} [CommRing B] [IsLocalRing B] [Field K]
variable [Algebra (ResidueField B) K] [Algebra B K] [IsScalarTower B (ResidueField B) K]
variable (pb : PowerBasis (ResidueField B) K) (F : Polynomial B)
variable (hF : F.map (residue B) = minpoly (ResidueField B) pb.gen)

/-- 持ち上げた最小多項式の閉ファイバーを指定体へ同定する基底環上の代数同型。 -/
noncomputable def liftedMinpolyClosedFibreEquiv :
    (AdjoinRoot F ⧸ (maximalIdeal B).map (algebraMap B (AdjoinRoot F))) ≃ₐ[B] K := by
  have h₁ : aeval (AdjoinRoot.root (F.map (residue B)))
      (minpoly (ResidueField B) pb.gen) = 0 := by
    rw [← hF, AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]
  have h₂ : aeval pb.gen (F.map (residue B)) = 0 := by
    rw [hF]
    exact minpoly.aeval _ _
  exact (adjoinRoot_closedFibreEquiv F).trans
    ((AdjoinRoot.equiv' (F.map (residue B)) pb h₁ h₂).restrictScalars B)

/-- 閉ファイバーの同型は、多項式の根を指定体の冪基底生成元へ送る。 -/
@[simp] theorem liftedMinpolyClosedFibreEquiv_root :
    liftedMinpolyClosedFibreEquiv pb F hF
      (Ideal.Quotient.mk _ (AdjoinRoot.root F)) = pb.gen := by
  simp only [liftedMinpolyClosedFibreEquiv, AlgEquiv.trans_apply,
    AlgEquiv.restrictScalars_apply, adjoinRoot_closedFibreEquiv_root]
  rw [← AlgEquiv.coe_toAlgHom, AdjoinRoot.equiv'_toAlgHom]
  -- aevalとeval₂の定義上の同一視を、Mathlibの根の計算への適用だけで展開する。
  with_unfolding_all exact AdjoinRoot.liftAlgHom_root _ _ _ _

end ClosedFibre

/-- 冪基底を持つ指定剰余体を、有限自由な平坦局所拡大として持ち上げる。
実際の環は持ち上げたモニック多項式の商。剰余体同型は基底の剰余体上で両立し、
多項式の根も指定された生成元へ送る。完備性・Noether性・分離性は要求しない。 -/
theorem exists_finite_free_local_extension_of_powerBasis
    (B K : Type u) [CommRing B] [IsLocalRing B] [Field K] [Algebra (ResidueField B) K]
    (pb : PowerBasis (ResidueField B) K) :
    ∃ (S : Type u) (_ : CommRing S) (_ : IsLocalRing S) (_ : Algebra B S)
      (_ : IsLocalHom (algebraMap B S)),
      Module.Free B S ∧ Module.Finite B S ∧ Module.Flat B S ∧
      (maximalIdeal B).map (algebraMap B S) = maximalIdeal S ∧
      ∃ e : ResidueField S ≃+* K,
        (∀ x, e (ResidueField.map (algebraMap B S) x) = algebraMap (ResidueField B) K x) ∧
        ∃ a : S, e (residue S a) = pb.gen := by
  classical
  let : Algebra B K := ((algebraMap (ResidueField B) K).comp (residue B)).toAlgebra
  let : IsScalarTower B (ResidueField B) K := IsScalarTower.of_algebraMap_eq (fun _ ↦ rfl)
  obtain ⟨F, hFmap, hFdegree, hFmonic⟩ :=
    exists_monic_residue_lift (minpoly (ResidueField B) pb.gen) (minpoly.monic pb.isIntegral_gen)
  let S := AdjoinRoot F
  let eq : (S ⧸ (maximalIdeal B).map (algebraMap B S)) ≃ₐ[B] K :=
    liftedMinpolyClosedFibreEquiv pb F hFmap
  have hfield : IsField (S ⧸ (maximalIdeal B).map (algebraMap B S)) :=
    MulEquiv.isField (Field.toIsField K) eq.toRingEquiv.toMulEquiv
  let : Algebra.IsIntegral B S := AdjoinRoot.isIntegral_of_monic hFmonic
  let : IsLocalRing S := isLocalRing_of_integral_of_field_closedFibre B S hfield
  have hmax : (maximalIdeal B).map (algebraMap B S) = maximalIdeal S :=
    maximalIdeal_map_eq_of_field_closedFibre B S hfield
  let : IsLocalHom (algebraMap B S) := AdjoinRoot.isLocalHom_of_monic_of_degree_pos hFmonic
    (by rw [hFdegree]; exact minpoly.degree_pos pb.isIntegral_gen)
  let e : ResidueField S ≃+* K := (Ideal.quotEquivOfEq hmax.symm).trans eq.toRingEquiv
  refine ⟨S, inferInstance, inferInstance, inferInstance, inferInstance,
    hFmonic.free_adjoinRoot, hFmonic.finite_adjoinRoot, (adjoinRoot_finite_flat F hFmonic).2,
    hmax, e, ?_, AdjoinRoot.root F, ?_⟩
  · intro x
    obtain ⟨b, rfl⟩ := residue_surjective (R := B) x
    rw [ResidueField.map_residue]
    change eq ((Ideal.quotEquivOfEq hmax.symm)
      (Ideal.Quotient.mk (maximalIdeal S) (algebraMap B S b))) = _
    rw [Ideal.quotEquivOfEq_mk]
    exact eq.commutes b
  · change eq ((Ideal.quotEquivOfEq hmax.symm)
      (Ideal.Quotient.mk (maximalIdeal S) (AdjoinRoot.root F))) = _
    rw [Ideal.quotEquivOfEq_mk]
    exact liftedMinpolyClosedFibreEquiv_root pb F hFmap

/-- 代数的な一元で生成された指定体について、同じ生成元に両立する局所拡大を構成する。
冪基底は一元による生成と整性から実際に作るため、分離的な原始元定理は不要。 -/
theorem exists_finite_free_local_extension_of_integral_generator
    (B K : Type u) [CommRing B] [IsLocalRing B] [Field K] [Algebra (ResidueField B) K]
    (a : K) (ha : IsIntegral (ResidueField B) a)
    (hgen : Algebra.adjoin (ResidueField B) {a} = ⊤) :
    ∃ (S : Type u) (_ : CommRing S) (_ : IsLocalRing S) (_ : Algebra B S)
      (_ : IsLocalHom (algebraMap B S)),
      Module.Free B S ∧ Module.Finite B S ∧ Module.Flat B S ∧
      (maximalIdeal B).map (algebraMap B S) = maximalIdeal S ∧
      ∃ e : ResidueField S ≃+* K,
        (∀ x, e (ResidueField.map (algebraMap B S) x) = algebraMap (ResidueField B) K x) ∧
        ∃ s : S, e (residue S s) = a := by
  simpa only [PowerBasis.ofAdjoinEqTop_gen] using
    exists_finite_free_local_extension_of_powerBasis B K (PowerBasis.ofAdjoinEqTop ha hgen)

/-- Noether局所環の代数的単生成剰余体拡大には、指定生成元と両立する完備Noether平坦局所拡大がある。
有限自由な局所拡大を実際に構成した後で完備化し、剰余体写像の全単射と自然性を使って
同型を移送する。基底環の完備性・剰余体拡大の分離性は要求しない。 -/
theorem exists_complete_flat_local_extension_of_integral_generator
    (B K : Type u) [CommRing B] [IsLocalRing B] [IsNoetherianRing B]
    [Field K] [Algebra (ResidueField B) K]
    (a : K) (ha : IsIntegral (ResidueField B) a)
    (hgen : Algebra.adjoin (ResidueField B) {a} = ⊤) :
    ∃ (C : Type u) (_ : CommRing C) (_ : IsLocalRing C) (_ : IsNoetherianRing C)
      (_ : IsAdicComplete (maximalIdeal C) C) (_ : Algebra B C)
      (_ : IsLocalHom (algebraMap B C)),
      Module.Flat B C ∧ (maximalIdeal B).map (algebraMap B C) = maximalIdeal C ∧
      ∃ e : ResidueField C ≃+* K,
        (∀ x, e (ResidueField.map (algebraMap B C) x) = algebraMap (ResidueField B) K x) ∧
        ∃ c : C, e (residue C c) = a := by
  obtain ⟨S, sRing, sLocal, sAlg, sHom, sFree, sFinite, sFlat, hsmax, eS, heS, s, hes⟩ :=
    exists_finite_free_local_extension_of_integral_generator B K a ha hgen
  let : IsNoetherianRing S := IsNoetherianRing.of_finite B S
  exact exists_complete_flat_local_extension_with_residue B S K hsmax eS heS a s hes

end SerrePositivity
