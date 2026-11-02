module

public import SerrePositivity.DifferentialGraded.Complexes.Cone
public import SerrePositivity.HomologicalAlgebra.CochainTensor.Cone
public import SerrePositivity.DifferentialGraded.Complexes.Perturbation
public import SerrePositivity.DifferentialGraded.Complexes.TensorCoproduct
public import SerrePositivity.HomologicalAlgebra.Complex.ConeLES
public import Mathlib.Algebra.Homology.HomotopyCategory.KProjective
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import SerrePositivity.DifferentialGraded.Complexes.MaurerCartanCurrying
public import Mathlib.CategoryTheory.Adjunction.Unique
public import Mathlib.Algebra.Homology.HomotopyCategory.SingleFunctors
public import SerrePositivity.DifferentialGraded.Complexes.TensorJoin
public import SerrePositivity.DifferentialGraded.Complexes.TensorZeroCochain

/-!
# Complexes.TensorShift

## 概要
14 本の同主題の構成と比較をまとめる。

## 方針
依存順に連結し、宣言と証明を保存する。

## 規約
元ごとの section で variable と option を保持する。private 名の変更は private_renames で明示する。

## 使われ方
DG の土台とその下流から import する。
-/

/-! ## TensorShift（旧 SerrePositivity/DifferentialGraded/Complexes/TensorShift.lean） -/

/-! # 左tensor因子のshift比較と全斉次Hom

通常のsign-freeな左shift比較が、dg作用のshift符号とも整合することを証明する。
-/

@[expose] public section TensorShift
universe u

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable {A : Type u} [CommRing A]

lemma tensorShiftLeft_apply (K P : Complex A) (s b c n : ℤ) (hbc : b + c = n)
    (x : (K⟦s⟧).X b) (y : P.X c) :
    (SerrePositivity.cochainTensorShiftLeft K P s).hom.f n
      (ιTensorObj (K⟦s⟧) P b c n hbc (x ⊗ₜ[A] y)) =
      ιTensorObj K P (b + s) c (n + s) (by omega) (x ⊗ₜ[A] y) := by
  have h := congrArg (fun f => f (x ⊗ₜ[A] y))
    (SerrePositivity.ιTensorObj_cochainTensorShiftLeft K P s b c n hbc)
  simp only [CochainComplex.shiftFunctorObjXIso, HomologicalComplex.XIsoOfEq_rfl,
    Iso.refl_hom, Iso.refl_inv, Category.comp_id] at h
  change (SerrePositivity.cochainTensorShiftLeft K P s).hom.f n
      (ιTensorObj (K⟦s⟧) P b c n hbc (x ⊗ₜ[A] y)) =
    (𝟙 (K.X (b + s)) ▷ P.X c ≫
      ιTensorObj K P (b + s) c (n + s) (by omega)) (x ⊗ₜ[A] y) at h
  rw [id_whiskerRight, Category.id_comp] at h
  exact h

/-- tensor–shift比較の全次数dg自然性。 -/
lemma tensorShiftLeft_hom_naturality (K P Q : Complex A) (s : ℤ) :
    tensorLeftHom (K⟦s⟧) P Q ≫
      homPostcompose ((K⟦s⟧) ⊗ P) (SerrePositivity.cochainTensorShiftLeft K Q s).hom =
    tensorLeftHom K P Q ≫ shiftHom s (K ⊗ P) (K ⊗ Q) ≫
      homPrecompose (SerrePositivity.cochainTensorShiftLeft K P s).hom ((K ⊗ Q)⟦s⟧) := by
  apply HomologicalComplex.Hom.ext
  funext p
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  apply Cochain.ext
  intro i j hij
  change (((tensorLeftHom (K⟦s⟧) P Q).f p a).comp
      (Cochain.ofHom (SerrePositivity.cochainTensorShiftLeft K Q s).hom) (add_zero p)).v i j hij =
    ((Cochain.ofHom (SerrePositivity.cochainTensorShiftLeft K P s).hom).comp
      ((shiftHom s (K ⊗ P) (K ⊗ Q)).f p ((tensorLeftHom K P Q).f p a)) (zero_add p)).v i j hij
  rw [Cochain.comp_zero_cochain_v, Cochain.zero_cochain_comp_v, Cochain.ofHom_v, Cochain.ofHom_v]
  apply mapBifunctor.hom_ext
  intro b c hbc
  change b + c = i at hbc
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro x y
  change (SerrePositivity.cochainTensorShiftLeft K Q s).hom.f j
      (((tensorLeftHom (K⟦s⟧) P Q).f p a).v i j hij
        (ιTensorObj (K⟦s⟧) P b c i hbc (x ⊗ₜ[A] y))) =
    (((shiftHom s (K ⊗ P) (K ⊗ Q)).f p ((tensorLeftHom K P Q).f p a)).v i j hij)
      ((SerrePositivity.cochainTensorShiftLeft K P s).hom.f i
        (ιTensorObj (K⟦s⟧) P b c i hbc (x ⊗ₜ[A] y)))
  rw [tensorLeftHom_apply]
  simp only [Units.smul_def, map_zsmul]
  rw [tensorShiftLeft_apply, tensorShiftLeft_apply, shiftHom_v]
  change (p * b).negOnePow • _ = (s * p).negOnePow •
    (((tensorLeftHom K P Q).f p a).v (i + s) (j + s) (by omega)
      (ιTensorObj K P (b + s) c (i + s) (by omega) (x ⊗ₜ[A] y)))
  rw [tensorLeftHom_apply, smul_smul]
  have hs : (s * p).negOnePow * (p * (b + s)).negOnePow = (p * b).negOnePow := by
    rw [mul_add, Int.negOnePow_add, mul_comm p s, mul_left_comm,
      Int.units_mul_self, mul_one]
  rw [hs]

end SerrePositivity.DifferentialGraded
end

end TensorShift

/-! ## TensorShiftSecondNaturality（旧 SerrePositivity/DifferentialGraded/Complexes/TensorShiftSecondNaturality.lean） -/

/-!
概要：左 tensor shift 比較の、シフトしない第二複体に関する自然性を公開する。
方針：各次数の同じ tensor 生成元で左 shift の符号なし公式を照合する。
規約：全整数 shift と非有界複体を扱う。
使われ方：c′ の sphere 係数抽出と元の Hom 鎖写像の可換性。
-/

@[expose] public section TensorShiftSecondNaturality
universe u

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory HomologicalComplex
variable (R : Type u) [CommRing R]

lemma tensorShiftLeft_second_naturality (P : Complex R) {K L : Complex R}
    (g : K ⟶ L) (s : ℤ) :
    (𝟙 (P⟦s⟧) ⊗ₘ g) ≫ (SerrePositivity.cochainTensorShiftLeft P L s).hom =
      (SerrePositivity.cochainTensorShiftLeft P K s).hom ≫ (𝟙 P ⊗ₘ g)⟦s⟧' := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply mapBifunctor.hom_ext
  intro b c hbc
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro x y
  change (SerrePositivity.cochainTensorShiftLeft P L s).hom.f n
    ((𝟙 (P⟦s⟧) ⊗ₘ g).f n
      (ιTensorObj (P⟦s⟧) K b c n hbc (x ⊗ₜ[R] y))) =
    ((𝟙 P ⊗ₘ g)⟦s⟧').f n
      ((SerrePositivity.cochainTensorShiftLeft P K s).hom.f n
        (ιTensorObj (P⟦s⟧) K b c n hbc (x ⊗ₜ[R] y)))
  rw [tensorMap_apply, tensorShiftLeft_apply, tensorShiftLeft_apply]
  change _ = (𝟙 P ⊗ₘ g).f (n + s) _
  rw [tensorMap_apply]
  rfl

end SerrePositivity.DifferentialGraded
end

end TensorShiftSecondNaturality

/-! ## QuasiIsoCycles（旧 SerrePositivity/DifferentialGraded/Complexes/QuasiIsoCycles.lean） -/

/-! # quasiIsoによるcycleの持ち上げと境界の反映

coneのacyclic性を用い、原像と境界の証人を具体的な要素として取り出す。
-/

@[expose] public section QuasiIsoCycles
universe u

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] {K L : Complex A}

lemma complexCone_d_fst (f : K ⟶ L) (q : ℤ) (z : (mappingCone f).X q) :
    (mappingCone.fst f).val.v (q + 1) (q + 1 + 1) rfl
      ((mappingCone f).d q (q + 1) z) =
        -K.d (q + 1) (q + 1 + 1) ((mappingCone.fst f).val.v q (q + 1) rfl z) :=
  congrArg (fun a => a z) (mappingCone.d_fst_v f q (q + 1) (q + 1 + 1) rfl rfl)

lemma complexCone_d_snd (f : K ⟶ L) (q : ℤ) (z : (mappingCone f).X q) :
    (mappingCone.snd f).v (q + 1) (q + 1) (add_zero _)
      ((mappingCone f).d q (q + 1) z) =
        f.f (q + 1) ((mappingCone.fst f).val.v q (q + 1) rfl z) +
          L.d q (q + 1) ((mappingCone.snd f).v q q (add_zero q) z) :=
  congrArg (fun a => a z) (mappingCone.d_snd_v f q (q + 1) rfl)

lemma complexAcyclic_boundary_succ {C : Complex A} (hC : C.Acyclic) (q : ℤ)
    (z : C.X (q + 1)) (hz : C.d (q + 1) (q + 1 + 1) z = 0) :
    ∃ t : C.X q, C.d q (q + 1) t = z := by
  have h := complexAcyclic_boundary (K := C) hC (q + 1) z hz
  rw [show q + 1 - 1 = q by omega] at h
  exact h

lemma complexQuasiIso_cycle_lift (f : K ⟶ L) (hf : QuasiIso f) (q : ℤ)
    (z : L.X (q + 1)) (hz : L.d (q + 1) (q + 1 + 1) z = 0) :
    ∃ a : K.X (q + 1), K.d (q + 1) (q + 1 + 1) a = 0 ∧
      ∃ b : L.X q, L.d q (q + 1) b = z - f.f (q + 1) a := by
  have hC := (complex_quasiIso_iff_acyclic_cone A f).1 hf
  have hinr : (mappingCone f).d (q + 1) (q + 1 + 1)
      ((mappingCone.inr f).f (q + 1) z) = 0 := by
    have h := congrArg (fun a => a z) ((mappingCone.inr f).comm (q + 1) (q + 1 + 1))
    change (mappingCone f).d (q + 1) (q + 1 + 1) ((mappingCone.inr f).f (q + 1) z) =
      (mappingCone.inr f).f (q + 1 + 1) (L.d (q + 1) (q + 1 + 1) z) at h
    exact h.trans (by rw [hz, map_zero])
  obtain ⟨t, ht⟩ := complexAcyclic_boundary_succ A hC q _ hinr
  let a := (mappingCone.fst f).val.v q (q + 1) rfl t
  let b := (mappingCone.snd f).v q q (add_zero q) t
  have hfst := complexCone_d_fst A f q t
  rw [ht, ← ModuleCat.comp_apply, mappingCone.inr_f_fst_v] at hfst
  have ha : K.d (q + 1) (q + 1 + 1) a = 0 := by
    change (0 : K.X (q + 1 + 1)) = -K.d (q + 1) (q + 1 + 1) a at hfst
    exact neg_eq_zero.mp hfst.symm
  have hsnd := complexCone_d_snd A f q t
  rw [ht, ← ModuleCat.comp_apply, mappingCone.inr_f_snd_v, ModuleCat.id_apply] at hsnd
  refine ⟨a, ha, b, ?_⟩
  change z = f.f (q + 1) a + L.d q (q + 1) b at hsnd
  exact eq_sub_of_add_eq ((add_comm _ _).trans hsnd.symm)

lemma complexQuasiIso_boundary_reflect (f : K ⟶ L) (hf : QuasiIso f) (q : ℤ)
    (a : K.X (q + 1)) (ha : K.d (q + 1) (q + 1 + 1) a = 0)
    (b : L.X q) (hb : L.d q (q + 1) b = f.f (q + 1) a) :
    ∃ t : K.X q, K.d q (q + 1) t = a := by
  let z := complexConeElementMk A f q a (-b)
  have hz : (mappingCone f).d q (q + 1) z = 0 := by
    apply complexConeElement_ext A f (q + 1)
    · rw [complexCone_d_fst, complexConeElementMk_fst, ha, neg_zero, map_zero]
    · rw [complexCone_d_snd, complexConeElementMk_fst, complexConeElementMk_snd,
        map_neg, hb, add_neg_cancel, map_zero]
  obtain ⟨s, hs⟩ := complexAcyclic_boundary
    (K := mappingCone f) ((complex_quasiIso_iff_acyclic_cone A f).1 hf) q z hz
  let t := -(mappingCone.fst f).val.v (q - 1) q (by omega) s
  refine ⟨t, ?_⟩
  have h := congrArg (fun a => a s) (mappingCone.d_fst_v' f q (q + 1) rfl)
  change (mappingCone.fst f).val.v q (q + 1) rfl ((mappingCone f).d (q - 1) q s) =
    -K.d q (q + 1) ((mappingCone.fst f).val.v (q - 1) q (by omega) s) at h
  rw [hs, complexConeElementMk_fst] at h
  exact (map_neg _ _).trans h.symm

end SerrePositivity.DifferentialGraded
end

end QuasiIsoCycles

/-! ## KProjectiveHom（旧 SerrePositivity/DifferentialGraded/Complexes/KProjectiveHom.lean） -/

/-! # K-projective複体からの全次数線形Homのacyclic性

次数nのcycleを値域のn shiftへの閉零射に移し、通常のchain homotopyを戻す。
戻す際の微分の符号をn.negOnePowで補正する。
-/

@[expose] public section KProjectiveHom
universe u

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A]

/-- K-projective複体からacyclic複体への全次数Homはacyclicである。 -/
lemma homComplex_acyclic_of_isKProjective (P N : Complex A) [P.IsKProjective]
    (hN : N.Acyclic) : (homComplex A P N).Acyclic := by
  intro n
  apply (HomologicalComplex.exactAt_iff' (K := homComplex A P N)
    (i := n - 1) (j := n) (k := n + 1) (by simp) (by simp)).2
  rw [ShortComplex.moduleCat_exact_iff]
  change ∀ z : Cochain P N n, δ n (n + 1) z = 0 →
    ∃ t : Cochain P N (n - 1), δ (n - 1) n t = z
  intro z hz
  let c : Cocycle P N n := Cocycle.mk z (n + 1) rfl hz
  let c' : Cocycle P (N⟦n⟧) 0 := c.rightShift n 0 (by omega)
  let f : P ⟶ N⟦n⟧ := Cocycle.homOf c'
  let h := IsKProjective.homotopyZero f (cochainAcyclic_shift hN n)
  refine ⟨n.negOnePow • (Cochain.ofHomotopy h).rightUnshift (n - 1) (by omega), ?_⟩
  rw [δ_units_smul, Cochain.δ_rightUnshift _ (n - 1) (by omega) n 0 (by omega),
    δ_ofHomotopy]
  simp only [Cochain.ofHom_zero, sub_zero, smul_smul, Int.units_mul_self, one_smul]
  change (Cochain.ofHom (Cocycle.homOf c')).rightUnshift n (by omega) = z
  have hc : Cochain.ofHom (Cocycle.homOf c') = c'.val := by
    exact congrArg Subtype.val (Cocycle.ofHom_homOf_eq_self c')
  rw [hc]
  exact Cochain.rightUnshift_rightShift z n 0 (by omega)

/-- 全次数Homによるacyclic性の判定はMathlibのK-projective条件も反映する。 -/
lemma isKProjective_of_homComplex_acyclic (P : Complex A)
    (hP : ∀ N : Complex A, N.Acyclic → (homComplex A P N).Acyclic) :
    P.IsKProjective where
  nonempty_homotopy_zero {L} f hL := by
    have he := (HomologicalComplex.exactAt_iff' (K := homComplex A P L)
      (i := -1) (j := 0) (k := 1) (by simp) (by simp)).1 (hP L hL 0)
    rw [ShortComplex.moduleCat_exact_iff] at he
    obtain ⟨t, ht⟩ := he (Cochain.ofHom f) (δ_ofHom f)
    refine ⟨(Cochain.equivHomotopy f 0).symm ⟨t, ?_⟩⟩
    rw [Cochain.ofHom_zero, add_zero]
    exact ht.symm

/-- 既存K-projective性と全次数線形Homの条件の同値。 -/
lemma isKProjective_iff_homComplex_acyclic (P : Complex A) :
    P.IsKProjective ↔ ∀ N : Complex A, N.Acyclic → (homComplex A P N).Acyclic :=
  ⟨fun _ N hN => homComplex_acyclic_of_isKProjective A P N hN,
    isKProjective_of_homComplex_acyclic A P⟩

end SerrePositivity.DifferentialGraded
end

end KProjectiveHom

/-! ## KProjectiveTensor（旧 SerrePositivity/DifferentialGraded/Complexes/KProjectiveTensor.lean） -/

/-! 全次数内部 Hom の随伴一意性による K-projective 複体の tensor 閉性。 -/

@[expose] public section KProjectiveTensor
universe u

noncomputable section
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory
variable (A : Type u) [CommRing A]

lemma complexTensor_isKProjective (P Q : Complex A) [P.IsKProjective] [Q.IsKProjective] :
    (P ⊗ Q).IsKProjective := by
  apply isKProjective_of_homComplex_acyclic A
  intro N hN
  let e := (ihom.adjunction (P ⊗ Q)).rightAdjointUniq
    (tensorClosed (complexClosed P) (complexClosed Q)).adj
  exact cochainAcyclic_of_iso
    (homComplex_acyclic_of_isKProjective A Q (homComplex A P N)
      (homComplex_acyclic_of_isKProjective A P N hN)) (e.app N).symm

end SerrePositivity.DifferentialGraded
end

end KProjectiveTensor

/-! ## CycleTransport（旧 SerrePositivity/DifferentialGraded/Complexes/CycleTransport.lean） -/

/-!
概要：実 cycle を複体同型と整数 shift に沿って線形に輸送する。
方針：同型の各次数成分と、shift 微分の可逆な符号を用いる。
規約：cycle の元を保持し、shift 後の次数は n+s とする。
使われ方：c′ のシフト自由閉射の元の Hom 係数を cycle として回収する。
-/

@[expose] public section CycleTransport
universe u

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (R : Type u) [CommRing R]

def complexCycleMap {P Q : Complex R} (f : P ⟶ Q) (n : ℤ) :
    complexCycles R P n →ₗ[R] complexCycles R Q n where
  toFun z := ⟨f.f n z.val, by
    have h := congrArg (fun φ => φ z.val) (f.comm n (n + 1))
    change Q.d n (n + 1) (f.f n z.val) = f.f (n + 1) (P.d n (n + 1) z.val) at h
    rw [z.property, map_zero] at h
    exact h⟩
  map_add' z w := Subtype.ext (map_add _ _ _)
  map_smul' r z := Subtype.ext (map_smul _ _ _)

def complexCycleIso {P Q : Complex R} (e : P ≅ Q) (n : ℤ) :
    complexCycles R P n ≃ₗ[R] complexCycles R Q n where
  toFun := complexCycleMap R e.hom n
  invFun := complexCycleMap R e.inv n
  left_inv z := by
    apply Subtype.ext
    exact congrArg (fun φ => φ.f n z.val) e.hom_inv_id
  right_inv z := by
    apply Subtype.ext
    exact congrArg (fun φ => φ.f n z.val) e.inv_hom_id
  map_add' := (complexCycleMap R e.hom n).map_add
  map_smul' := (complexCycleMap R e.hom n).map_smul

def complexShiftCycleIso (K : Complex R) (s n : ℤ) :
    complexCycles R (K⟦s⟧) n ≃ₗ[R] complexCycles R K (n + s) where
  toFun z := ⟨z.val, by
    have h : s.negOnePow • K.d (n + s) (n + 1 + s) z.val = 0 := z.property
    rw [show n + 1 + s = n + s + 1 by omega] at h
    exact (smul_eq_zero_iff_eq s.negOnePow).mp h⟩
  invFun z := ⟨z.val, by
    change s.negOnePow • K.d (n + s) (n + 1 + s) z.val = 0
    rw [show n + 1 + s = n + s + 1 by omega, z.property, smul_zero]⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end SerrePositivity.DifferentialGraded
end

end CycleTransport

/-! ## SphereTensorShift（旧 SerrePositivity/DifferentialGraded/Complexes/SphereTensorShift.lean） -/

/-!
概要：自由 sphere と任意複体の tensor を、同じ複体の整数 shift へ同定する。
方針：sphere を shift した単位複体と比較し、左 tensor shift と左単位を合成する。
規約：非有界複体・全整数次数を扱い、元の tensor を保つ。
使われ方：c′ のシフト自由加群間閉射から元の Hom の斉次係数を取り出す。
-/

@[expose] public section SphereTensorShift
universe u

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory
variable (R : Type u) [CommRing R]

def complexSphereUnitShiftIso (n : ℤ) : complexSphere R n ≅ (𝟙_ (Complex R))⟦-n⟧ :=
  (((CochainComplex.singleFunctors (ModuleCat.{u} R)).shiftIso (-n) n 0 (by omega)).app
    (𝟙_ (ModuleCat R))).symm

def complexSphereTensorShiftIso (n : ℤ) (K : Complex R) :
    complexSphere R n ⊗ K ≅ K⟦-n⟧ :=
  (tensorIso (complexSphereUnitShiftIso R n) (Iso.refl K)) ≪≫
    SerrePositivity.cochainTensorShiftLeft (𝟙_ (Complex R)) K (-n) ≪≫
    (shiftFunctor (Complex R) (-n)).mapIso (λ_ K)

end SerrePositivity.DifferentialGraded
end

end SphereTensorShift

/-! ## SphereTensorShiftNaturality（旧 SerrePositivity/DifferentialGraded/Complexes/SphereTensorShiftNaturality.lean） -/

/-!
概要：sphere tensor shift 同型の任意の Hom 鎖写像に関する自然性を証明する。
方針：tensor の交換則、左 shift の第二変数自然性、左単位の自然性を合成する。
規約：元の sphere 同型と元の鎖写像をそのまま使う。
使われ方：c′ の自由閉射の係数評価と実延長の比較。
-/

@[expose] public section SphereTensorShiftNaturality
universe u

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory
variable (R : Type u) [CommRing R]

lemma complexSphereTensorShiftIso_naturality (n : ℤ) {K L : Complex R} (g : K ⟶ L) :
    (𝟙 (complexSphere R n) ⊗ₘ g) ≫ (complexSphereTensorShiftIso R n L).hom =
      (complexSphereTensorShiftIso R n K).hom ≫ g⟦-n⟧' := by
  have ht : (𝟙 (complexSphere R n) ⊗ₘ g) ≫
      ((complexSphereUnitShiftIso R n).hom ⊗ₘ 𝟙 L) =
      ((complexSphereUnitShiftIso R n).hom ⊗ₘ 𝟙 K) ≫
        (𝟙 ((𝟙_ (Complex R))⟦-n⟧) ⊗ₘ g) := by
    simp only [tensorHom_comp_tensorHom, Category.id_comp, Category.comp_id]
  have hu : (𝟙 (𝟙_ (Complex R)) ⊗ₘ g)⟦-n⟧' ≫ ((λ_ L).hom)⟦-n⟧' =
      ((λ_ K).hom)⟦-n⟧' ≫ g⟦-n⟧' := by
    rw [← Functor.map_comp, ← Functor.map_comp]
    exact congrArg (shiftFunctor (Complex R) (-n)).map (leftUnitor_naturality g)
  simp only [complexSphereTensorShiftIso, Iso.trans_hom, tensorIso_hom,
    CategoryTheory.Functor.mapIso_hom, Iso.refl_hom]
  rw [← Category.assoc, ← Category.assoc, ht]
  simp only [Category.assoc]
  rw [← Category.assoc (𝟙 ((𝟙_ (Complex R))⟦-n⟧) ⊗ₘ g),
    tensorShiftLeft_second_naturality R (𝟙_ (Complex R)) g (-n)]
  simp only [Category.assoc]
  rw [hu]

end SerrePositivity.DifferentialGraded
end

end SphereTensorShiftNaturality

/-! ## PrefixTensorCochain（旧 SerrePositivity/DifferentialGraded/Complexes/PrefixTensorCochain.lean） -/

/-! # 前方二因子を保った右tensorの括弧変更とcochainの整合性 -/

@[expose] public section PrefixTensorCochain
universe u

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable {A : Type u} [CommRing A]

/-- 二つの固定前方因子の後のcochainは、右tensorの括弧変更と可換する。 -/
lemma prefixTensor_cochain_middle (K E P P' Q : Complex A) (p : ℤ) (f : Cochain P P' p) :
    ((tensorRightHom Q (K ⊗ (E ⊗ P)) (K ⊗ (E ⊗ P'))).f p
      ((tensorLeftHom K (E ⊗ P) (E ⊗ P')).f p ((tensorLeftHom E P P').f p f))).comp
      (Cochain.ofHom ((α_ K (E ⊗ P') Q).hom ≫ K ◁ (α_ E P' Q).hom)) (add_zero p) =
    (Cochain.ofHom ((α_ K (E ⊗ P) Q).hom ≫ K ◁ (α_ E P Q).hom)).comp
      ((tensorLeftHom K (E ⊗ (P ⊗ Q)) (E ⊗ (P' ⊗ Q))).f p
        ((tensorLeftHom E (P ⊗ Q) (P' ⊗ Q)).f p
          ((tensorRightHom Q P P').f p f))) (zero_add p) := by
  rw [Cochain.ofHom_comp, Cochain.ofHom_comp,
    ← Cochain.comp_assoc_of_second_is_zero_cochain,
    associator_hom_cochain_middle,
    Cochain.comp_assoc_of_first_is_zero_cochain,
    ← tensorLeftHom_ofHom, ← tensorLeftHom_cochain_comp,
    associator_hom_cochain_middle, tensorLeftHom_cochain_comp, tensorLeftHom_ofHom,
    ← Cochain.comp_assoc_of_first_is_zero_cochain]

/-- 最後の右因子のcochainも、二つの固定前方因子の括弧変更と可換する。 -/
lemma prefixTensor_cochain_right (K E P Q Q' : Complex A) (p : ℤ) (f : Cochain Q Q' p) :
    ((tensorLeftHom (K ⊗ (E ⊗ P)) Q Q').f p f).comp
      (Cochain.ofHom ((α_ K (E ⊗ P) Q').hom ≫ K ◁ (α_ E P Q').hom)) (add_zero p) =
    (Cochain.ofHom ((α_ K (E ⊗ P) Q).hom ≫ K ◁ (α_ E P Q).hom)).comp
      ((tensorLeftHom K (E ⊗ (P ⊗ Q)) (E ⊗ (P ⊗ Q'))).f p
        ((tensorLeftHom E (P ⊗ Q) (P ⊗ Q')).f p
          ((tensorLeftHom P Q Q').f p f))) (zero_add p) := by
  rw [Cochain.ofHom_comp, Cochain.ofHom_comp,
    ← Cochain.comp_assoc_of_second_is_zero_cochain,
    associator_hom_cochain_right,
    Cochain.comp_assoc_of_first_is_zero_cochain,
    ← tensorLeftHom_ofHom, ← tensorLeftHom_cochain_comp,
    associator_hom_cochain_right, tensorLeftHom_cochain_comp, tensorLeftHom_ofHom,
    ← Cochain.comp_assoc_of_first_is_zero_cochain]

end SerrePositivity.DifferentialGraded
end

end PrefixTensorCochain

/-! ## PrefixTensorCochainPostcompose（旧 SerrePositivity/DifferentialGraded/Complexes/PrefixTensorCochainPostcompose.lean） -/

/-! # 前方二因子を保つcochain輸送と後合成

## 概要
前方二因子を保つcochain輸送と後合成。

## 方針
既存の全dg自然なHom・作用・chain mapと局所化の計算を再利用する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。dg加群の導来作用・準同値比較の基盤。任意可換環上のMorita・K理論のモデル比較に再利用できる。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section PrefixTensorCochainPostcompose
universe u

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable {A : Type u} [CommRing A]

lemma prefixTensor_cochain_middle_postcompose (K E P P' Q T V : Complex A) (p : ℤ)
    (f : Cochain P P' p) (m : P' ⊗ Q ⟶ T) (h : K ⊗ (E ⊗ T) ⟶ V) :
    ((tensorRightHom Q (K ⊗ (E ⊗ P)) (K ⊗ (E ⊗ P'))).f p
      ((tensorLeftHom K (E ⊗ P) (E ⊗ P')).f p ((tensorLeftHom E P P').f p f))).comp
      (Cochain.ofHom ((α_ K (E ⊗ P') Q).hom ≫ K ◁ (α_ E P' Q).hom ≫
        K ◁ (E ◁ m) ≫ h)) (add_zero p) =
    ((Cochain.ofHom ((α_ K (E ⊗ P) Q).hom ≫ K ◁ (α_ E P Q).hom)).comp
      ((tensorLeftHom K (E ⊗ (P ⊗ Q)) (E ⊗ T)).f p
        ((tensorLeftHom E (P ⊗ Q) T).f p
          (((tensorRightHom Q P P').f p f).comp (Cochain.ofHom m) (add_zero p))))
      (zero_add p)).comp (Cochain.ofHom h) (add_zero p) := by
  rw [tensorLeftHom_cochain_comp, tensorLeftHom_ofHom,
    tensorLeftHom_cochain_comp, tensorLeftHom_ofHom]
  have hp := congrArg (fun c : Cochain ((K ⊗ (E ⊗ P)) ⊗ Q)
      (K ⊗ (E ⊗ (P' ⊗ Q))) p =>
    c.comp (Cochain.ofHom (K ◁ (E ◁ m) ≫ h)) (add_zero p))
    (prefixTensor_cochain_middle K E P P' Q p f)
  simp only [Cochain.ofHom_comp,
    ← Cochain.comp_assoc_of_first_is_zero_cochain,
    ← Cochain.comp_assoc_of_second_is_zero_cochain] at hp ⊢
  exact hp

lemma prefixTensor_cochain_right_postcompose (K E P Q Q' T V : Complex A) (p : ℤ)
    (f : Cochain Q Q' p) (m : P ⊗ Q' ⟶ T) (h : K ⊗ (E ⊗ T) ⟶ V) :
    ((tensorLeftHom (K ⊗ (E ⊗ P)) Q Q').f p f).comp
      (Cochain.ofHom ((α_ K (E ⊗ P) Q').hom ≫ K ◁ (α_ E P Q').hom ≫
        K ◁ (E ◁ m) ≫ h)) (add_zero p) =
    ((Cochain.ofHom ((α_ K (E ⊗ P) Q).hom ≫ K ◁ (α_ E P Q).hom)).comp
      ((tensorLeftHom K (E ⊗ (P ⊗ Q)) (E ⊗ T)).f p
        ((tensorLeftHom E (P ⊗ Q) T).f p
          (((tensorLeftHom P Q Q').f p f).comp (Cochain.ofHom m) (add_zero p))))
      (zero_add p)).comp (Cochain.ofHom h) (add_zero p) := by
  rw [tensorLeftHom_cochain_comp, tensorLeftHom_ofHom,
    tensorLeftHom_cochain_comp, tensorLeftHom_ofHom]
  have hp := congrArg (fun c : Cochain ((K ⊗ (E ⊗ P)) ⊗ Q)
      (K ⊗ (E ⊗ (P ⊗ Q'))) p =>
    c.comp (Cochain.ofHom (K ◁ (E ◁ m) ≫ h)) (add_zero p))
    (prefixTensor_cochain_right K E P Q Q' p f)
  simp only [Cochain.ofHom_comp,
    ← Cochain.comp_assoc_of_first_is_zero_cochain,
    ← Cochain.comp_assoc_of_second_is_zero_cochain] at hp ⊢
  exact hp

end SerrePositivity.DifferentialGraded
end

end PrefixTensorCochainPostcompose

/-! ## PrefixTensorCochainAction（旧 SerrePositivity/DifferentialGraded/Complexes/PrefixTensorCochainAction.lean） -/

/-! # 結合的な先頭追加と後方cochainの持ち上げ

## 概要
結合的な先頭追加と後方cochainの持ち上げ。

## 方針
既存の全dg自然なHom・作用・chain mapと局所化の計算を再利用する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。dg加群の導来作用・準同値比較の基盤。任意可換環上のMorita・K理論のモデル比較に再利用できる。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section PrefixTensorCochainAction
universe u

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable {A : Type u} [CommRing A]

lemma prefixTensor_cochain_action_left (K E P P' Q R T V : Complex A) (p : ℤ)
    (f : Cochain P P' p) (pre : K ⊗ (E ⊗ P') ⟶ R) (cmp : R ⊗ Q ⟶ V)
    (m : P' ⊗ Q ⟶ T) (post : K ⊗ (E ⊗ T) ⟶ V)
    (ha : (pre ▷ Q) ≫ cmp = (α_ K (E ⊗ P') Q).hom ≫ K ◁ (α_ E P' Q).hom ≫
      K ◁ (E ◁ m) ≫ post) :
    ((tensorRightHom Q (K ⊗ (E ⊗ P)) R).f p
      (((tensorLeftHom K (E ⊗ P) (E ⊗ P')).f p ((tensorLeftHom E P P').f p f)).comp
        (Cochain.ofHom pre) (add_zero p))).comp (Cochain.ofHom cmp) (add_zero p) =
    ((Cochain.ofHom ((α_ K (E ⊗ P) Q).hom ≫ K ◁ (α_ E P Q).hom)).comp
      ((tensorLeftHom K (E ⊗ (P ⊗ Q)) (E ⊗ T)).f p
        ((tensorLeftHom E (P ⊗ Q) T).f p
          (((tensorRightHom Q P P').f p f).comp (Cochain.ofHom m) (add_zero p))))
      (zero_add p)).comp (Cochain.ofHom post) (add_zero p) := by
  rw [tensorRightHom_cochain_comp, tensorRightHom_ofHom,
    Cochain.comp_assoc_of_third_is_zero_cochain, ← Cochain.ofHom_comp, ha]
  exact prefixTensor_cochain_middle_postcompose K E P P' Q T V p f m post

lemma prefixTensor_cochain_action_right (K E P Q Q' T V : Complex A) (p : ℤ)
    (f : Cochain Q Q' p) (cmp : (K ⊗ (E ⊗ P)) ⊗ Q' ⟶ V)
    (m : P ⊗ Q' ⟶ T) (post : K ⊗ (E ⊗ T) ⟶ V)
    (ha : cmp = (α_ K (E ⊗ P) Q').hom ≫ K ◁ (α_ E P Q').hom ≫ K ◁ (E ◁ m) ≫ post) :
    ((tensorLeftHom (K ⊗ (E ⊗ P)) Q Q').f p f).comp (Cochain.ofHom cmp) (add_zero p) =
    ((Cochain.ofHom ((α_ K (E ⊗ P) Q).hom ≫ K ◁ (α_ E P Q).hom)).comp
      ((tensorLeftHom K (E ⊗ (P ⊗ Q)) (E ⊗ T)).f p
        ((tensorLeftHom E (P ⊗ Q) T).f p
          (((tensorLeftHom P Q Q').f p f).comp (Cochain.ofHom m) (add_zero p))))
      (zero_add p)).comp (Cochain.ofHom post) (add_zero p) := by
  rw [ha]
  exact prefixTensor_cochain_right_postcompose K E P Q Q' T V p f m post

end SerrePositivity.DifferentialGraded
end

end PrefixTensorCochainAction

/-! ## RightTripleCochainExt（旧 SerrePositivity/DifferentialGraded/Complexes/RightTripleCochainExt.lean） -/

/-! # 右括弧三重tensor上の任意次数cochainの判定 -/

@[expose] public section RightTripleCochainExt
universe u

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable {A : Type u} [CommRing A]

lemma rightTripleCochain_ext {P Q R T : Complex A} {p : ℤ}
    (f g : Cochain (P ⊗ (Q ⊗ R)) T p)
    (h : ∀ (i j k a n : ℤ) (ha : i + (j + k) = a) (hn : a + p = n)
      (x : P.X i) (y : Q.X j) (z : R.X k),
      f.v a n hn (ιTensorObj P (Q ⊗ R) i (j + k) a ha
        (x ⊗ₜ[A] ιTensorObj Q R j k (j + k) rfl (y ⊗ₜ[A] z))) =
      g.v a n hn (ιTensorObj P (Q ⊗ R) i (j + k) a ha
        (x ⊗ₜ[A] ιTensorObj Q R j k (j + k) rfl (y ⊗ₜ[A] z)))) : f = g := by
  apply Cochain.ext
  intro a n hn
  apply (cancel_epi ((α_ P Q R).hom.f a)).1
  apply SerrePositivity.cochainTensorTriple_hom_ext P Q R a
  intro i j k ha
  apply ModuleCat.hom_ext
  apply TensorProduct.ext_threefold
  intro x y z
  change f.v a n hn ((α_ P Q R).hom.f a
      (ιTensorObj (P ⊗ Q) R (i + j) k a ha
        (ιTensorObj P Q i j (i + j) rfl (x ⊗ₜ[A] y) ⊗ₜ[A] z))) =
    g.v a n hn ((α_ P Q R).hom.f a
      (ιTensorObj (P ⊗ Q) R (i + j) k a ha
        (ιTensorObj P Q i j (i + j) rfl (x ⊗ₜ[A] y) ⊗ₜ[A] z)))
  simpa only [associator_apply] using h i j k a n (by omega) hn x y z

lemma rightTripleCochain_ext₀ {P Q R T : Complex A}
    (f g : Cochain (P ⊗ (Q ⊗ R)) T 0)
    (h : ∀ (i j k n : ℤ) (hn : i + (j + k) = n)
      (x : P.X i) (y : Q.X j) (z : R.X k),
      f.v n n (add_zero n) (ιTensorObj P (Q ⊗ R) i (j + k) n hn
        (x ⊗ₜ[A] ιTensorObj Q R j k (j + k) rfl (y ⊗ₜ[A] z))) =
      g.v n n (add_zero n) (ιTensorObj P (Q ⊗ R) i (j + k) n hn
        (x ⊗ₜ[A] ιTensorObj Q R j k (j + k) rfl (y ⊗ₜ[A] z)))) : f = g := by
  apply Cochain.ext₀
  intro n
  apply (cancel_epi ((α_ P Q R).hom.f n)).1
  apply SerrePositivity.cochainTensorTriple_hom_ext P Q R n
  intro i j k hn
  apply ModuleCat.hom_ext
  apply TensorProduct.ext_threefold
  intro x y z
  change f.v n n (add_zero n) ((α_ P Q R).hom.f n
      (ιTensorObj (P ⊗ Q) R (i + j) k n hn
        (ιTensorObj P Q i j (i + j) rfl (x ⊗ₜ[A] y) ⊗ₜ[A] z))) =
    g.v n n (add_zero n) ((α_ P Q R).hom.f n
      (ιTensorObj (P ⊗ Q) R (i + j) k n hn
        (ιTensorObj P Q i j (i + j) rfl (x ⊗ₜ[A] y) ⊗ₜ[A] z)))
  simpa only [associator_apply] using h i j k n (by omega) x y z

end SerrePositivity.DifferentialGraded
end

end RightTripleCochainExt

/-! ## SphereCochainExt（旧 SerrePositivity/DifferentialGraded/Complexes/SphereCochainExt.lean） -/

/-! # 任意次数sphereの標準生成元上のcochain判定

## 概要
任意次数sphereの標準生成元上のcochain判定。

## 方針
既存の全dg自然なHom・作用・chain mapと局所化の計算を再利用する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。dg加群の導来作用・準同値比較の基盤。任意可換環上のMorita・K理論のモデル比較に再利用できる。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section SphereCochainExt
universe u

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A]

lemma sphere_generator_span (d : ℤ) (e : (complexSphere A d).X d) :
    e = ((singleObjXSelf (.up ℤ) d (𝟙_ (ModuleCat.{u} A))).hom e) •
      ((singleObjXSelf (.up ℤ) d (𝟙_ (ModuleCat.{u} A))).inv (1 : A)) := by
  calc
    e = (singleObjXSelf (.up ℤ) d (𝟙_ (ModuleCat.{u} A))).inv
        ((singleObjXSelf (.up ℤ) d (𝟙_ (ModuleCat.{u} A))).hom e) := by
      change e = ((singleObjXSelf (.up ℤ) d (𝟙_ (ModuleCat.{u} A))).hom ≫
        (singleObjXSelf (.up ℤ) d (𝟙_ (ModuleCat.{u} A))).inv) e
      rw [Iso.hom_inv_id]
      rfl
    _ = _ := by rw [← map_smul]; simp only [smul_eq_mul, mul_one]

lemma sphereMiddleCochain_ext₀ (d : ℤ) {K P T : Complex A}
    (f g : Cochain (K ⊗ (complexSphere A d ⊗ P)) T 0)
    (h : ∀ (i j n : ℤ) (hn : i + (d + j) = n) (x : K.X i) (y : P.X j),
      f.v n n (add_zero n) (ιTensorObj K (complexSphere A d ⊗ P) i (d + j) n hn
        (x ⊗ₜ[A] ιTensorObj (complexSphere A d) P d j (d + j) rfl
          ((singleObjXSelf (.up ℤ) d (𝟙_ (ModuleCat.{u} A))).inv (1 : A) ⊗ₜ[A] y))) =
      g.v n n (add_zero n) (ιTensorObj K (complexSphere A d ⊗ P) i (d + j) n hn
        (x ⊗ₜ[A] ιTensorObj (complexSphere A d) P d j (d + j) rfl
          ((singleObjXSelf (.up ℤ) d (𝟙_ (ModuleCat.{u} A))).inv (1 : A) ⊗ₜ[A] y)))) :
    f = g := by
  apply rightTripleCochain_ext₀
  intro i k j n hn x e y
  by_cases hk : k = d
  · subst k
    rw [sphere_generator_span A d e]
    simp only [TensorProduct.smul_tmul, TensorProduct.tmul_smul, map_smul]
    rw [h i j n hn x y]
  · let := ModuleCat.subsingleton_of_isZero
      (isZero_single_obj_X (.up ℤ) d (𝟙_ (ModuleCat.{u} A)) k hk)
    have he : e = 0 := Subsingleton.elim _ _
    rw [he]
    simp only [TensorProduct.zero_tmul, TensorProduct.tmul_zero, map_zero]

end SerrePositivity.DifferentialGraded
end

end SphereCochainExt

/-! ## TensorJoinEvaluation（旧 SerrePositivity/DifferentialGraded/Complexes/TensorJoinEvaluation.lean） -/

/-! # 前方二因子の写像による合成と後方cochainの評価 -/

@[expose] public section TensorJoinEvaluation
universe u

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable {A : Type u} [CommRing A]

/-- 前方の合成を保つ写像と結合的な後方作用による、任意次数0 cochainの評価式。 -/
lemma tensorJoin_evaluation (U V W U' V' W' R T Y Z : Complex A)
    (F : U ⟶ U') (G : V ⟶ V') (H : W ⟶ W')
    (c : U ⊗ V ⟶ W) (c' : U' ⊗ V' ⟶ W')
    (d : W' ⊗ T ⟶ Z) (e : V' ⊗ T ⟶ Y) (k : U' ⊗ Y ⟶ Z)
    (hc : c ≫ H = (F ⊗ₘ G) ≫ c')
    (ha : (c' ▷ T) ≫ d = (α_ U' V' T).hom ≫ U' ◁ e ≫ k)
    (r : Cochain R T 0) :
    (Cochain.ofHom ((α_ U V R).inv ≫ c ▷ R)).comp
      ((tensorZeroCochain (Cochain.ofHom H) r).comp (Cochain.ofHom d) (zero_add 0))
      (zero_add 0) =
    (tensorZeroCochain (Cochain.ofHom F)
      ((tensorZeroCochain (Cochain.ofHom G) r).comp (Cochain.ofHom e) (zero_add 0))).comp
        (Cochain.ofHom k) (zero_add 0) := by
  apply rightTripleCochain_ext₀
  intro i j l a ha' x y z
  simp only [cochain_ofHom_comp_apply, chain_comp_apply, associator_inv_apply,
    whiskerRight_apply, cochain_comp_ofHom_apply, tensorZeroCochain_apply,
    Cochain.ofHom_v]
  have hmap := congrArg (fun f : U ⊗ V ⟶ W' =>
    f.f (i + j) (ιTensorObj U V i j (i + j) rfl (x ⊗ₜ[A] y))) hc
  simp only [chain_comp_apply, tensorMap_apply] at hmap
  rw [hmap]
  exact tensorComposition_assoc_apply U' V' T W' Y Z c' d e k ha i j l a (by omega)
    (F.f i x) (G.f j y) (r.v l l (add_zero l) z)

end SerrePositivity.DifferentialGraded
end

end TensorJoinEvaluation
