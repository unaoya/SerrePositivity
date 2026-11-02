module

public import SerrePositivity.DifferentialGraded.Complexes.TensorZeroCochain
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexShift
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
public import SerrePositivity.HomologicalAlgebra.Complex.Cone
public import SerrePositivity.DifferentialGraded.Complexes.Perturbation
public import Mathlib.Algebra.Homology.HomotopyCategory.Triangulated
public import SerrePositivity.DifferentialGraded.Module.Basic
public import SerrePositivity.DifferentialGraded.Complexes.HomLimits

/-!
# Complexes.Cone

## 概要
17 本の同主題の構成と比較をまとめる。

## 方針
依存順に連結し、宣言と証明を保存する。

## 規約
元ごとの section で variable と option を保持する。private 名の変更は private_renames で明示する。

## 使われ方
DG の土台とその下流から import する。
-/

/-! ## Shift（旧 SerrePositivity/DifferentialGraded/Complexes/Shift.lean） -/

/-! # 整数 shift の全次数 dg 関手

Mathlib の cochain shift は Hom 微分を (-1)^s 倍する。
次数 p の Hom には (-1)^(sp) を掛け、chain map を得る。
-/

@[expose] public section Shift
universe u

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable {A : Type u} [CommRing A]

/-- 整数 shift の Hom chain map。 -/
def shiftHom (s : ℤ) (P Q : Complex A) :
    homComplex A P Q ⟶ homComplex A (P⟦s⟧) (Q⟦s⟧) where
  f p := ModuleCat.ofHom ((s * p).negOnePow • Cochain.shiftLinearMap A P Q p s)
  comm' p q hpq := by
    obtain rfl : q = p + 1 := hpq.symm
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro f
    change δ p (p + 1) ((s * p).negOnePow • f.shift s) =
      (s * (p + 1)).negOnePow • (δ p (p + 1) f).shift s
    rw [δ_units_smul, Cochain.δ_shift, smul_smul, ← Int.negOnePow_add]
    congr 2
    ring

/-- 斉次 Hom の shift は射の次数と shift の Koszul 符号を持つ。 -/
lemma shiftHom_apply (s : ℤ) (P Q : Complex A) (p : ℤ) (f : Homogeneous P Q p) :
    (shiftHom s P Q).f p f = (s * p).negOnePow • f.shift s := rfl

/-- shift の全斉次成分。 -/
lemma shiftHom_v (s : ℤ) (P Q : Complex A) (p i j : ℤ) (hij : i + p = j)
    (f : Homogeneous P Q p) :
    ((shiftHom s P Q).f p f).v i j hij =
      (s * p).negOnePow • f.v (i + s) (j + s) (by omega) := by
  rw [shiftHom_apply, Cochain.units_smul_v, Cochain.shift_v']

/-- 閉零次数では Mathlib の通常の chain map shift と一致する。 -/
lemma shiftHom_ofHom (s : ℤ) {P Q : Complex A} (f : P ⟶ Q) :
    (shiftHom s P Q).f 0 (Cochain.ofHom f) = Cochain.ofHom (f⟦s⟧') := by
  apply Cochain.ext₀
  intro i
  rw [shiftHom_v]
  simp only [mul_zero, Int.negOnePow_zero, one_smul, Cochain.ofHom_v]
  rfl

/-- shift の Hom chain map は閉単位を保存する。 -/
lemma shiftHom_identity (s : ℤ) (P : Complex A) :
    identity P ≫ shiftHom s P P = identity (P⟦s⟧) := by
  apply (unitCycleEquiv _).injective
  apply Subtype.ext
  change (cycleFromUnit _ (identity P ≫ shiftHom s P P)).val =
    (cycleFromUnit _ (identity (P⟦s⟧))).val
  rw [cycleFromUnit_postcomp]
  simp only [identity, cycleFromUnit_unitFromCycle]
  rw [shiftHom_ofHom, CategoryTheory.Functor.map_id]

/-- shift の Hom chain map は豊穣合成を保存する。 -/
lemma shiftHom_comp (s : ℤ) (P Q T : Complex A) :
    enrichedComposition P Q T ≫ shiftHom s P T =
      (shiftHom s P Q ⊗ₘ shiftHom s Q T) ≫ enrichedComposition _ _ _ := by
  apply tensorHom_ext
  intro p q n hn
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro f g
  change (shiftHom s P T).f n
    ((enrichedComposition P Q T).f n
      (ιTensorObj (homComplex A P Q) (homComplex A Q T) p q n hn (f ⊗ₜ[A] g))) =
    (enrichedComposition _ _ _).f n
      ((shiftHom s P Q ⊗ₘ shiftHom s Q T).f n
        (ιTensorObj (homComplex A P Q) (homComplex A Q T) p q n hn (f ⊗ₜ[A] g)))
  rw [tensorMap_apply, enrichedComposition_apply, enrichedComposition_apply,
    shiftHom_apply, shiftHom_apply, shiftHom_apply]
  simp only [Cochain.shift_units_smul, Cochain.units_smul_comp, Cochain.comp_units_smul, smul_smul]
  apply Cochain.ext
  intro i j hij
  rw [Cochain.units_smul_v, Cochain.units_smul_v, Cochain.shift_v',
    Cochain.comp_v _ _ hn (i + s) (i + p + s) (j + s) (by omega) (by omega),
    Cochain.comp_v _ _ hn i (i + p) j rfl (by omega),
    Cochain.shift_v', Cochain.shift_v']
  have he : (s * n).negOnePow * (p * q).negOnePow =
      (p * q).negOnePow * ((s * p).negOnePow * (s * q).negOnePow) := by
    rw [← Int.negOnePow_add, ← Int.negOnePow_add, ← Int.negOnePow_add]
    congr 1
    rw [← hn]
    ring
  rw [he, mul_comm (s * p).negOnePow (s * q).negOnePow]

/-- Mathlib の複体 shift を全次数に拡張した主 dg 関手。 -/
def shiftDG (s : ℤ) : DGFunctor A (Complex A) (Complex A) where
  obj P := P⟦s⟧
  map := shiftHom s
  map_id := shiftHom_identity s
  map_comp := shiftHom_comp s
end SerrePositivity.DifferentialGraded
end

end Shift

/-! ## ShiftCoherence（旧 SerrePositivity/DifferentialGraded/Complexes/ShiftCoherence.lean） -/

/-! # 零・加法 shift 比較の全次数自然性 -/

@[expose] public section ShiftCoherence
universe u

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory HomologicalComplex CochainComplex HomComplex
variable {A : Type u} [CommRing A]

/-- cochain の始域次数の輸送は XIsoOfEq の前合成。 -/
lemma homogeneous_XIsoOfEq_hom_comp {P Q : Complex A} {p i i' j : ℤ}
    (f : Homogeneous P Q p) (hi : i = i') (hij : i' + p = j) :
    (P.XIsoOfEq hi).hom ≫ f.v i' j hij = f.v i j (by omega) := by
  subst i'
  simp only [HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom, Category.id_comp]

/-- Mathlib の零 shift 比較は全次数 Hom に対して自然。 -/
lemma shiftHom_zero_naturality (P Q : Complex A) :
    shiftHom 0 P Q ≫ homPostcompose (P⟦(0 : ℤ)⟧)
      ((shiftFunctorZero (Complex A) ℤ).hom.app Q) =
    homPrecompose ((shiftFunctorZero (Complex A) ℤ).hom.app P) Q := by
  apply HomologicalComplex.Hom.ext
  funext p
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro f
  apply Cochain.ext
  intro i j hij
  change (((shiftHom 0 P Q).f p f).comp
    (Cochain.ofHom ((shiftFunctorZero (Complex A) ℤ).hom.app Q)) (add_zero p)).v i j hij =
    ((Cochain.ofHom ((shiftFunctorZero (Complex A) ℤ).hom.app P)).comp f
      (zero_add p)).v i j hij
  rw [Cochain.comp_zero_cochain_v, Cochain.zero_cochain_comp_v,
    Cochain.ofHom_v, Cochain.ofHom_v, shiftHom_v]
  simp only [zero_mul, Int.negOnePow_zero, one_smul,
    CochainComplex.shiftFunctorZero_hom_app_f]
  rw [Cochain.v_comp_XIsoOfEq_hom, homogeneous_XIsoOfEq_hom_comp]

/-- Mathlib の加法 shift 比較は全次数 Hom に対して自然。 -/
lemma shiftHom_add_naturality (s t : ℤ) (P Q : Complex A) :
    shiftHom (s + t) P Q ≫ homPostcompose (P⟦s + t⟧)
      ((shiftFunctorAdd (Complex A) s t).hom.app Q) =
    shiftHom s P Q ≫ shiftHom t (P⟦s⟧) (Q⟦s⟧) ≫
      homPrecompose ((shiftFunctorAdd (Complex A) s t).hom.app P) ((Q⟦s⟧)⟦t⟧) := by
  apply HomologicalComplex.Hom.ext
  funext p
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro f
  apply Cochain.ext
  intro i j hij
  change (((shiftHom (s + t) P Q).f p f).comp
    (Cochain.ofHom ((shiftFunctorAdd (Complex A) s t).hom.app Q)) (add_zero p)).v i j hij =
    ((Cochain.ofHom ((shiftFunctorAdd (Complex A) s t).hom.app P)).comp
      ((shiftHom t (P⟦s⟧) (Q⟦s⟧)).f p ((shiftHom s P Q).f p f))
      (zero_add p)).v i j hij
  rw [Cochain.comp_zero_cochain_v, Cochain.zero_cochain_comp_v,
    Cochain.ofHom_v, Cochain.ofHom_v, shiftHom_v, shiftHom_v, shiftHom_v]
  simp only [CochainComplex.shiftFunctorAdd_hom_app_f,
    Linear.units_smul_comp, Linear.comp_units_smul, smul_smul]
  rw [Cochain.v_comp_XIsoOfEq_hom, homogeneous_XIsoOfEq_hom_comp]
  rw [← Int.negOnePow_add]
  congr 1
  congr 1
  ring
end SerrePositivity.DifferentialGraded
end

end ShiftCoherence

/-! ## ShiftRepresentation（旧 SerrePositivity/DifferentialGraded/Complexes/ShiftRepresentation.lean） -/

/-! # 互いに逆な斉次cochainによるshiftの表示 -/

@[expose] public section ShiftRepresentation
universe u

noncomputable section
namespace SerrePositivity.DifferentialGraded
open CategoryTheory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] {K L : Complex A} {s : ℤ}
variable (α : Cochain K L s) (hα : δ s (s + 1) α = 0)

/-- 閉じた次数sのcochainが定めるK→L[s]。 -/
def complexShiftComparison : K ⟶ L⟦s⟧ :=
  Cocycle.equivHomShift.symm (Cocycle.mk α (s + 1) rfl hα)

lemma complexShiftComparison_f (i : ℤ) :
    (complexShiftComparison A α hα).f i = α.v i (i + s) rfl := by
  simp only [complexShiftComparison, Cocycle.equivHomShift_symm_apply,
    Cocycle.homOf_f, Cocycle.rightShift_coe, Cocycle.mk_coe]
  rw [Cochain.rightShift_v _ s 0 (zero_add s) i i (add_zero i) (i + s) rfl]
  simp only [CochainComplex.shiftFunctorObjXIso, HomologicalComplex.XIsoOfEq_rfl,
    Iso.refl_inv, Category.comp_id]

lemma complexShiftComparison_bijective (β : Cochain L K (-s))
    (hαβ : α.comp β (add_neg_cancel s) = Cochain.ofHom (𝟙 K))
    (hβα : β.comp α (neg_add_cancel s) = Cochain.ofHom (𝟙 L)) (i : ℤ) :
    Function.Bijective ((complexShiftComparison A α hα).f i) := by
  let ψ : L.X (i + s) → K.X i := β.v (i + s) i (by omega)
  have hl : Function.LeftInverse ψ ((complexShiftComparison A α hα).f i) := by
    intro z
    have h := Cochain.congr_v hαβ i i (add_zero i)
    rw [Cochain.comp_v _ _ _ i (i + s) i rfl (by omega), Cochain.ofHom_v, id_f] at h
    have hz := congrArg (fun f => f z) h
    simp only [ModuleCat.comp_apply, ModuleCat.id_apply] at hz
    rw [complexShiftComparison_f]
    exact hz
  have hr : Function.RightInverse ψ ((complexShiftComparison A α hα).f i) := by
    intro z
    have h := Cochain.congr_v hβα (i + s) (i + s) (add_zero (i + s))
    rw [Cochain.comp_v _ _ _ (i + s) i (i + s) (by omega) rfl, Cochain.ofHom_v, id_f] at h
    have hz := congrArg (fun f => f z) h
    simp only [ModuleCat.comp_apply, ModuleCat.id_apply] at hz
    rw [complexShiftComparison_f]
    exact hz
  exact ⟨hl.injective, hr.surjective⟩

lemma complexShiftComparison_isIso (β : Cochain L K (-s))
    (hαβ : α.comp β (add_neg_cancel s) = Cochain.ofHom (𝟙 K))
    (hβα : β.comp α (neg_add_cancel s) = Cochain.ofHom (𝟙 L)) :
    IsIso (complexShiftComparison A α hα) := by
  have (i : ℤ) : IsIso ((complexShiftComparison A α hα).f i) :=
    (ConcreteCategory.isIso_iff_bijective _).2 (complexShiftComparison_bijective A α hα β hαβ hβα i)
  exact HomologicalComplex.Hom.isIso_of_components _

/-- 次数sと−sの逆なcochainから得られる実際のshift同型。 -/
def complexShiftIso (β : Cochain L K (-s))
    (hαβ : α.comp β (add_neg_cancel s) = Cochain.ofHom (𝟙 K))
    (hβα : β.comp α (neg_add_cancel s) = Cochain.ofHom (𝟙 L)) : K ≅ L⟦s⟧ := by
  have := complexShiftComparison_isIso A α hα β hαβ hβα
  exact asIso (complexShiftComparison A α hα)

/-- 逆cochainの次数を任意のtで指定する版。 -/
def complexShiftIsoOfSumZero {t : ℤ} (β : Cochain L K t) (hst : s + t = 0)
    (hαβ : α.comp β hst = Cochain.ofHom (𝟙 K))
    (hβα : β.comp α (by omega : t + s = 0) = Cochain.ofHom (𝟙 L)) : K ≅ L⟦s⟧ := by
  have ht : t = -s := by omega
  subst t
  exact complexShiftIso A α hα β hαβ hβα

end SerrePositivity.DifferentialGraded
end

end ShiftRepresentation

/-! ## Cone（旧 SerrePositivity/DifferentialGraded/Complexes/Cone.lean） -/

/-! # 閉零射の cone に作用する全次数対角 cochain

cone の左成分は +1 shift なので、次数 p の作用に (-1)^p が入る。
Mathlib の mappingCone とその射影・包含を再利用する。
-/

@[expose] public section Cone
universe u

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits HomologicalComplex CochainComplex HomComplex
variable {A : Type u} [CommRing A] {P Q R S : Complex A}

/-- 二つの斉次射を cone 上の符号付き対角 cochain にする。 -/
def coneMapCochain (f : P ⟶ Q) (g : R ⟶ S) {p : ℤ}
    (a : Homogeneous P R p) (b : Homogeneous Q S p) :
    Homogeneous (mappingCone f) (mappingCone g) p :=
  mappingCone.liftCochain g
    (p.negOnePow • (mappingCone.fst f).val.comp a (by omega : 1 + p = p + 1))
    ((mappingCone.snd f).comp b (zero_add p)) rfl

/-- 第一射影後の cone 作用は shift の Koszul 符号を持つ。 -/
lemma coneMapCochain_fst (f : P ⟶ Q) (g : R ⟶ S) {p : ℤ}
    (a : Homogeneous P R p) (b : Homogeneous Q S p) :
    (coneMapCochain f g a b).comp (mappingCone.fst g).val rfl =
      p.negOnePow • (mappingCone.fst f).val.comp a (by omega : 1 + p = p + 1) :=
  mappingCone.liftCochain_fst _ _ _ _

/-- 第二射影後の cone 作用は第二成分の作用。 -/
lemma coneMapCochain_snd (f : P ⟶ Q) (g : R ⟶ S) {p : ℤ}
    (a : Homogeneous P R p) (b : Homogeneous Q S p) :
    (coneMapCochain f g a b).comp (mappingCone.snd g) (add_zero p) =
      (mappingCone.snd f).comp b (zero_add p) :=
  mappingCone.liftCochain_snd _ _ _ _

/-- 全斉次次数の cone 作用の成分公式。 -/
lemma coneMapCochain_v (f : P ⟶ Q) (g : R ⟶ S) {p : ℤ}
    (a : Homogeneous P R p) (b : Homogeneous Q S p)
    (i j : ℤ) (hij : i + p = j) :
    (coneMapCochain f g a b).v i j hij =
      p.negOnePow • ((mappingCone.fst f).val.v i (i + 1) rfl ≫
        a.v (i + 1) (j + 1) (by omega) ≫
          (mappingCone.inl g).v (j + 1) j (by omega)) +
      (mappingCone.snd f).v i i (add_zero i) ≫ b.v i j hij ≫ (mappingCone.inr g).f j := by
  simp only [coneMapCochain, mappingCone.liftCochain, Cochain.add_v,
    Cochain.comp_v _ _ (by omega : (p + 1) + (-1) = p) i (j + 1) j (by omega) (by omega),
    Cochain.comp_zero_cochain_v, Cochain.zero_cochain_comp_v,
    Cochain.units_smul_v, Cochain.ofHom_v,
    Cochain.comp_v _ _ (by omega : 1 + p = p + 1) i (i + 1) (j + 1) rfl (by omega),
    Linear.units_smul_comp, Category.assoc]

/-- 対角 cone 作用は加法を保存する。 -/
lemma coneMapCochain_add (f : P ⟶ Q) (g : R ⟶ S) {p : ℤ}
    (a a' : Homogeneous P R p) (b b' : Homogeneous Q S p) :
    coneMapCochain f g (a + a') (b + b') =
      coneMapCochain f g a b + coneMapCochain f g a' b' := by
  simp only [coneMapCochain, mappingCone.liftCochain, Cochain.comp_add, smul_add,
    Cochain.add_comp]
  abel

/-- 対角 cone 作用は係数環のスカラー倍を保存する。 -/
lemma coneMapCochain_smul (f : P ⟶ Q) (g : R ⟶ S) {p : ℤ}
    (a : Homogeneous P R p) (b : Homogeneous Q S p) (r : A) :
    coneMapCochain f g (r • a) (r • b) = r • coneMapCochain f g a b := by
  simp only [coneMapCochain, mappingCone.liftCochain, Cochain.comp_smul,
    Cochain.smul_comp, smul_add]
  rw [smul_comm p.negOnePow r]
  simp only [Cochain.smul_comp]

/-- 対角 cone 作用は整数単位の符号倍を保存する。 -/
lemma coneMapCochain_units_smul (f : P ⟶ Q) (g : R ⟶ S) {p : ℤ}
    (a : Homogeneous P R p) (b : Homogeneous Q S p) (r : ℤˣ) :
    coneMapCochain f g (r • a) (r • b) = r • coneMapCochain f g a b := by
  simp only [coneMapCochain, mappingCone.liftCochain, Cochain.comp_units_smul,
    Cochain.units_smul_comp, smul_add]
  rw [smul_comm p.negOnePow r]

/-- 次数零の恒等対角作用は cone の恒等 cochain。 -/
lemma coneMapCochain_identity (f : P ⟶ Q) :
    coneMapCochain f f (Cochain.ofHom (𝟙 P)) (Cochain.ofHom (𝟙 Q)) =
      Cochain.ofHom (𝟙 (mappingCone f)) := by
  apply (mappingCone.ext_cochain_to_iff f 0 1 rfl).2
  constructor
  · rw [coneMapCochain_fst]
    simp only [Int.negOnePow_zero, one_smul, Cochain.comp_id, Cochain.id_comp]
  · rw [coneMapCochain_snd]
    simp only [Cochain.comp_id, Cochain.id_comp]

/-- 可換な斉次 square に対して、cone 対角作用は Hom 微分と可換。 -/
lemma coneMapCochain_differential (f : P ⟶ Q) (g : R ⟶ S) {p : ℤ}
    (a : Homogeneous P R p) (b : Homogeneous Q S p)
    (h : a.comp (Cochain.ofHom g) (add_zero p) =
      (Cochain.ofHom f).comp b (zero_add p)) :
    δ p (p + 1) (coneMapCochain f g a b) =
      coneMapCochain f g (δ p (p + 1) a) (δ p (p + 1) b) := by
  unfold coneMapCochain
  rw [mappingCone.δ_liftCochain g _ _ rfl (p + 1 + 1) rfl]
  rw [δ_units_smul, δ_comp (mappingCone.fst f).val a (by omega : 1 + p = p + 1)
    2 (p + 1) (p + 1 + 1) rfl rfl rfl]
  simp only [Cocycle.δ_eq_zero, Cochain.zero_comp, smul_zero, add_zero]
  rw [δ_comp (mappingCone.snd f) b (zero_add p) 1 (p + 1) (p + 1) rfl
    (zero_add 1) rfl, mappingCone.δ_snd]
  simp only [Cochain.units_smul_comp,
    Cochain.neg_comp, smul_neg]
  rw [Cochain.comp_assoc_of_second_is_zero_cochain,
    Cochain.comp_assoc_of_third_is_zero_cochain, h]
  simp only [add_assoc, neg_add_cancel, add_zero]
  simp only [mappingCone.liftCochain, Int.negOnePow_succ, Units.neg_smul,
    Cochain.neg_comp, Cochain.units_smul_comp]

/-- 対角 cone 作用は通常順の全斉次合成を保存する。 -/
lemma coneMapCochain_comp {T U : Complex A}
    (f : P ⟶ Q) (g : R ⟶ S) (h : T ⟶ U) {p q n : ℤ}
    (a : Homogeneous P R p) (b : Homogeneous Q S p)
    (c : Homogeneous R T q) (d : Homogeneous S U q) (hn : p + q = n) :
    (coneMapCochain f g a b).comp (coneMapCochain g h c d) hn =
      coneMapCochain f h (a.comp c hn) (b.comp d hn) := by
  apply (mappingCone.ext_cochain_to_iff h n (n + 1) rfl).2
  constructor
  · rw [Cochain.comp_assoc _ _ _ hn rfl (by omega), coneMapCochain_fst,
      Cochain.comp_units_smul]
    rw [← Cochain.comp_assoc _ _ _ rfl (by omega : 1 + q = q + 1) (by omega),
      coneMapCochain_fst, Cochain.units_smul_comp,
      Cochain.comp_assoc _ _ _ (by omega : 1 + p = p + 1) hn (by omega),
      coneMapCochain_fst, smul_smul, ← Int.negOnePow_add]
    congr 1
    congr 1
    omega
  · rw [Cochain.comp_assoc_of_third_is_zero_cochain, coneMapCochain_snd,
      ← Cochain.comp_assoc_of_second_is_zero_cochain, coneMapCochain_snd,
      Cochain.comp_assoc_of_first_is_zero_cochain, coneMapCochain_snd]

/-- cone の標準包含は全次数対角作用と可換。 -/
lemma coneMapCochain_inr (f : P ⟶ Q) (g : R ⟶ S) {p : ℤ}
    (a : Homogeneous P R p) (b : Homogeneous Q S p) :
    (Cochain.ofHom (mappingCone.inr f)).comp (coneMapCochain f g a b) (zero_add p) =
      b.comp (Cochain.ofHom (mappingCone.inr g)) (add_zero p) := by
  apply Cochain.ext
  intro i j hij
  rw [Cochain.zero_cochain_comp_v, Cochain.comp_zero_cochain_v,
    Cochain.ofHom_v, Cochain.ofHom_v, coneMapCochain_v]
  simp only [Preadditive.comp_add, Linear.comp_units_smul,
    mappingCone.inr_f_fst_v_assoc, mappingCone.inr_f_snd_v_assoc,
    zero_comp, smul_zero, zero_add]
end SerrePositivity.DifferentialGraded
end

end Cone

/-! ## ConeHom（旧 SerrePositivity/DifferentialGraded/Complexes/ConeHom.lean） -/

/-! # 全次数で可換する square から cone の Hom chain map -/

@[expose] public section ConeHom
universe u

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory HomologicalComplex CochainComplex HomComplex
variable {A : Type u} [CommRing A] {K P Q R S : Complex A}

/-- 可換 square の成分を斉次 cochain の可換式として読む。 -/
lemma coneHom_square_apply (f : P ⟶ Q) (g : R ⟶ S)
    (a : K ⟶ homComplex A P R) (b : K ⟶ homComplex A Q S)
    (h : a ≫ homPostcompose P g = b ≫ homPrecompose f S) (p : ℤ) (t : K.X p) :
    (a.f p t).comp (Cochain.ofHom g) (add_zero p) =
      (Cochain.ofHom f).comp (b.f p t) (zero_add p) :=
  congrArg (fun l => l.f p t) h

/-- 可換 square の Hom chain map を cone の Hom chain map にする。 -/
def coneHomMap (f : P ⟶ Q) (g : R ⟶ S)
    (a : K ⟶ homComplex A P R) (b : K ⟶ homComplex A Q S)
    (h : a ≫ homPostcompose P g = b ≫ homPrecompose f S) :
    K ⟶ homComplex A (mappingCone f) (mappingCone g) where
  f p := ModuleCat.ofHom
    { toFun t := coneMapCochain f g (a.f p t) (b.f p t)
      map_add' t t' := by rw [map_add, map_add, coneMapCochain_add]
      map_smul' r t := by
        rw [map_smul, map_smul, coneMapCochain_smul]
        rfl }
  comm' p q hpq := by
    obtain rfl : q = p + 1 := hpq.symm
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro t
    change δ p (p + 1) (coneMapCochain f g (a.f p t) (b.f p t)) =
      coneMapCochain f g (a.f (p + 1) (K.d p (p + 1) t))
        (b.f (p + 1) (K.d p (p + 1) t))
    rw [coneMapCochain_differential f g _ _ (coneHom_square_apply f g a b h p t)]
    have ha := congrArg (fun l : K.X p ⟶ (homComplex A P R).X (p + 1) => l t)
      (a.comm p (p + 1))
    have hb := congrArg (fun l : K.X p ⟶ (homComplex A Q S).X (p + 1) => l t)
      (b.comm p (p + 1))
    change δ p (p + 1) (a.f p t) = a.f (p + 1) (K.d p (p + 1) t) at ha
    change δ p (p + 1) (b.f p t) = b.f (p + 1) (K.d p (p + 1) t) at hb
    rw [ha, hb]

/-- cone Hom chain map の成分は符号付き対角 cochain。 -/
lemma coneHomMap_apply (f : P ⟶ Q) (g : R ⟶ S)
    (a : K ⟶ homComplex A P R) (b : K ⟶ homComplex A Q S) (h)
    (p : ℤ) (t : K.X p) :
    (coneHomMap f g a b h).f p t = coneMapCochain f g (a.f p t) (b.f p t) := rfl

/-- cone の標準包含の全次数 Hom 自然性。 -/
lemma coneHomMap_inr (f : P ⟶ Q) (g : R ⟶ S)
    (a : K ⟶ homComplex A P R) (b : K ⟶ homComplex A Q S) (h) :
    b ≫ homPostcompose Q (mappingCone.inr g) =
      coneHomMap f g a b h ≫ homPrecompose (mappingCone.inr f) (mappingCone g) := by
  apply HomologicalComplex.Hom.ext
  funext p
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro t
  exact (coneMapCochain_inr f g (a.f p t) (b.f p t)).symm
end SerrePositivity.DifferentialGraded
end

end ConeHom

/-! ## ConeMaps（旧 SerrePositivity/DifferentialGraded/Complexes/ConeMaps.lean） -/

/-! # cone の connecting map の全次数自然性 -/

@[expose] public section ConeMaps
universe u

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits HomologicalComplex CochainComplex HomComplex
variable {A : Type u} [CommRing A] {K P Q R S : Complex A}

/-- cone の第一射影後の作用の斉次成分。 -/
lemma coneMapCochain_fst_v (f : P ⟶ Q) (g : R ⟶ S) {p : ℤ}
    (a : Homogeneous P R p) (b : Homogeneous Q S p)
    (i j : ℤ) (hij : i + p = j) :
    (coneMapCochain f g a b).v i j hij ≫ (mappingCone.fst g).val.v j (j + 1) rfl =
      p.negOnePow • ((mappingCone.fst f).val.v i (i + 1) rfl ≫
        a.v (i + 1) (j + 1) (by omega)) := by
  have h := Cochain.congr_v (coneMapCochain_fst f g a b) i (j + 1) (by omega)
  simpa only [Cochain.units_smul_v,
    Cochain.comp_v _ _ (by omega : p + 1 = p + 1) i j (j + 1) hij rfl,
    Cochain.comp_v _ _ (by omega : 1 + p = p + 1) i (i + 1) (j + 1) rfl (by omega)] using h

/-- 既存 cone triangle の connecting map は全次数 Hom に対して自然。 -/
lemma coneHomMap_connecting (f : P ⟶ Q) (g : R ⟶ S)
    (a : K ⟶ homComplex A P R) (b : K ⟶ homComplex A Q S) (h) :
    coneHomMap f g a b h ≫ homPostcompose (mappingCone f) (mappingCone.triangle g).mor₃ =
      a ≫ shiftHom 1 P R ≫ homPrecompose (mappingCone.triangle f).mor₃ (R⟦(1 : ℤ)⟧) := by
  apply HomologicalComplex.Hom.ext
  funext p
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro t
  apply Cochain.ext
  intro i j hij
  change ((coneMapCochain f g (a.f p t) (b.f p t)).comp
    (Cochain.ofHom (mappingCone.triangle g).mor₃) (add_zero p)).v i j hij =
    ((Cochain.ofHom (mappingCone.triangle f).mor₃).comp
      ((shiftHom 1 P R).f p (a.f p t)) (zero_add p)).v i j hij
  rw [Cochain.comp_zero_cochain_v, Cochain.zero_cochain_comp_v,
    Cochain.ofHom_v, Cochain.ofHom_v, shiftHom_v,
    SerrePositivity.coneTriangle_mor₃_f, SerrePositivity.coneTriangle_mor₃_f]
  simp only [CochainComplex.shiftFunctorObjXIso, HomologicalComplex.XIsoOfEq_rfl,
    Iso.refl_inv, Category.comp_id, one_mul, Preadditive.comp_neg]
  rw [coneMapCochain_fst_v]
  simp only [Preadditive.neg_comp, Linear.comp_units_smul, smul_neg]

/-- 閉次数0の cone 対角作用は Mathlib の可換 square の cone 射と一致。 -/
lemma coneMapCochain_ofHom (f : P ⟶ Q) (g : R ⟶ S)
    (a : P ⟶ R) (b : Q ⟶ S) (h : f ≫ b = a ≫ g) :
    Cochain.ofHom (mappingCone.map f g a b h) =
      coneMapCochain f g (Cochain.ofHom a) (Cochain.ofHom b) := by
  apply Cochain.ext₀
  intro i
  rw [Cochain.ofHom_v, coneMapCochain_v]
  apply mappingCone.ext_from f (i + 1) i rfl
  · simp only [mappingCone.map, mappingCone.inl_v_desc_f,
      Cochain.zero_cochain_comp_v, Cochain.ofHom_v, Int.negOnePow_zero, one_smul,
      Preadditive.comp_add, mappingCone.inl_v_fst_v_assoc,
      mappingCone.inl_v_snd_v_assoc, zero_comp, add_zero]
  · simp only [mappingCone.map, mappingCone.inr_f_desc_f, HomologicalComplex.comp_f,
      Cochain.ofHom_v, Int.negOnePow_zero, one_smul, Preadditive.comp_add,
      mappingCone.inr_f_fst_v_assoc, mappingCone.inr_f_snd_v_assoc,
      zero_comp, zero_add]
end SerrePositivity.DifferentialGraded
end

end ConeMaps

/-! ## ConeDesc（旧 SerrePositivity/DifferentialGraded/Complexes/ConeDesc.lean） -/

/-! # 合成が零となる射のconeからの延長 -/

@[expose] public section ConeDesc
universe u

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits HomologicalComplex CochainComplex HomComplex
variable {A : Type u} [CommRing A]

def complexConeDesc {P Q T : Complex A} (f : P ⟶ Q) (q : Q ⟶ T) (h : f ≫ q = 0) :
    mappingCone f ⟶ T := mappingCone.desc f 0 q (by simp [h])

lemma complexConeDesc_f {P Q T : Complex A} (f : P ⟶ Q) (q : Q ⟶ T) (h : f ≫ q = 0)
    (i : ℤ) : (complexConeDesc f q h).f i =
      (mappingCone.snd f).v i i (add_zero i) ≫ q.f i := by
  rw [complexConeDesc, mappingCone.desc_f _ _ _ _ i (i + 1) rfl,
    Cochain.zero_v, comp_zero, zero_add]

lemma complexConeDesc_ofHom {P Q T : Complex A} (f : P ⟶ Q) (q : Q ⟶ T) (h : f ≫ q = 0) :
    Cochain.ofHom (complexConeDesc f q h) =
      (mappingCone.snd f).comp (Cochain.ofHom q) (zero_add 0) := by
  apply Cochain.ext₀
  intro i
  rw [Cochain.ofHom_v, complexConeDesc_f, Cochain.comp_zero_cochain_v, Cochain.ofHom_v]

lemma complexConeDesc_inr {P Q T : Complex A} (f : P ⟶ Q) (q : Q ⟶ T) (h : f ≫ q = 0) :
    mappingCone.inr f ≫ complexConeDesc f q h = q := mappingCone.inr_desc _ _ _ _

/-- coneの全次数対角作用と零cochain延長の整合性。 -/
lemma coneMapCochain_desc {P Q T P' Q' T' : Complex A}
    (f : P ⟶ Q) (g : P' ⟶ Q') (q : Q ⟶ T) (q' : Q' ⟶ T')
    (hq : f ≫ q = 0) (hq' : g ≫ q' = 0) {p : ℤ}
    (a : Cochain P P' p) (b : Cochain Q Q' p) (c : Cochain T T' p)
    (hb : b.comp (Cochain.ofHom q') (add_zero p) =
      (Cochain.ofHom q).comp c (zero_add p)) :
    (coneMapCochain f g a b).comp (Cochain.ofHom (complexConeDesc g q' hq')) (add_zero p) =
      (Cochain.ofHom (complexConeDesc f q hq)).comp c (zero_add p) := by
  rw [complexConeDesc_ofHom, complexConeDesc_ofHom,
    ← Cochain.comp_assoc_of_second_is_zero_cochain, coneMapCochain_snd,
    Cochain.comp_assoc_of_first_is_zero_cochain, hb,
    ← Cochain.comp_assoc_of_second_is_zero_cochain]

/-- source cycleの像を消す具体的な境界の証人。 -/
def complexConeBoundaryWitness {P Q : Complex A} (f : P ⟶ Q) (n : ℤ)
    (z : complexCycles A P (n + 1)) : (mappingCone f).X n :=
  homotopyCofiber.inlX f (n + 1) n rfl z.val

lemma complexConeBoundaryWitness_d {P Q : Complex A} (f : P ⟶ Q) (n : ℤ)
    (z : complexCycles A P (n + 1)) :
    (mappingCone f).d n (n + 1) (complexConeBoundaryWitness f n z) =
      (mappingCone.inr f).f (n + 1) (f.f (n + 1) z.val) := by
  let t := homotopyCofiber.inlX f (n + 1) n rfl z.val
  have h := congrArg (fun k => k z.val)
    (homotopyCofiber.inlX_d f n (n + 1) (n + 1 + 1) rfl rfl)
  change homotopyCofiber.d f n (n + 1) t =
    -homotopyCofiber.inlX f (n + 1 + 1) (n + 1) rfl (P.d (n + 1) (n + 1 + 1) z.val) +
      homotopyCofiber.inrX f (n + 1) (f.f (n + 1) z.val) at h
  rw [z.property, map_zero, neg_zero, zero_add] at h
  exact h

/-- 零cochainによるcone延長は、この境界の証人を零に送る。 -/
lemma complexConeBoundaryWitness_desc {P Q T : Complex A} (f : P ⟶ Q) (q : Q ⟶ T)
    (h : f ≫ q = 0) (n : ℤ) (z : complexCycles A P (n + 1)) :
    (complexConeDesc f q h).f n (complexConeBoundaryWitness f n z) = 0 := by
  have hv := congrArg (fun k => k z.val)
    (mappingCone.inl_v_desc_f f 0 q (by simp [h]) (n + 1) n (by omega))
  exact hv

/-- sourceのcycleの像は標準coneで境界となる。 -/
lemma complexCone_inl_boundary {P Q : Complex A} (f : P ⟶ Q) (n : ℤ)
    (z : complexCycles A P (n + 1)) :
    ∃ t : (mappingCone f).X n, (mappingCone f).d n (n + 1) t =
      (mappingCone.inr f).f (n + 1) (f.f (n + 1) z.val) :=
  ⟨complexConeBoundaryWitness f n z, complexConeBoundaryWitness_d f n z⟩

end SerrePositivity.DifferentialGraded
end

end ConeDesc

/-! ## ConeShift（旧 SerrePositivity/DifferentialGraded/Complexes/ConeShift.lean） -/

/-! # 明示的なshift射を用いる既存cone shift同型 -/

@[expose] public section ConeShift
universe u

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits HomologicalComplex CochainComplex HomComplex
variable {A : Type u} [CommRing A] {K L : Complex A}

def complexConeShiftIso (f : K ⟶ L) (s : ℤ) (ψ : K⟦s⟧ ⟶ L⟦s⟧) (hψ : ψ = f⟦s⟧') :
    (mappingCone f)⟦s⟧ ≅ mappingCone ψ := by
  subst ψ
  exact mappingCone.shiftIso f s

lemma complexConeShiftIso_hom_cochain (f : K ⟶ L) (s : ℤ) (ψ : K⟦s⟧ ⟶ L⟦s⟧)
    (hψ : ψ = f⟦s⟧') :
    Cochain.ofHom (complexConeShiftIso f s ψ hψ).hom =
      mappingCone.liftCochain ψ (s.negOnePow • (mappingCone.fst f).val.shift s)
        ((mappingCone.snd f).shift s) (zero_add 1) := by
  subst ψ
  simp only [complexConeShiftIso, mappingCone.shiftIso, mappingCone.ofHom_lift,
    Cocycle.coe_units_smul, Cocycle.shift_coe]

lemma complexConeShiftIso_inv_cochain (f : K ⟶ L) (s : ℤ) (ψ : K⟦s⟧ ⟶ L⟦s⟧)
    (hψ : ψ = f⟦s⟧') :
    Cochain.ofHom (complexConeShiftIso f s ψ hψ).inv =
      mappingCone.descCochain ψ (s.negOnePow • (mappingCone.inl f).shift s)
        (Cochain.ofHom ((mappingCone.inr f)⟦s⟧')) (neg_add_cancel 1) := by
  subst ψ
  simp only [complexConeShiftIso, mappingCone.shiftIso, mappingCone.ofHom_desc]

lemma complexConeShift_lift_condition (f : K ⟶ L) (s : ℤ) (ψ : K⟦s⟧ ⟶ L⟦s⟧)
    (hψ : ψ = f⟦s⟧') :
    δ 0 1 ((mappingCone.snd f).shift s) +
      (s.negOnePow • (mappingCone.fst f).val.shift s).comp (Cochain.ofHom ψ) (add_zero 1) = 0 := by
  subst ψ
  ext p q hpq
  dsimp
  simp only [Cochain.δ_shift, mappingCone.δ_snd, Cochain.shift_neg, smul_neg, Cochain.neg_v,
    shiftFunctor_obj_X', Cochain.units_smul_v, Cochain.shift_v', Cochain.comp_zero_cochain_v,
    Cochain.ofHom_v, Cochain.units_smul_comp, shiftFunctor_map_f']
  simp

lemma complexConeShift_desc_condition (f : K ⟶ L) (s : ℤ) (ψ : K⟦s⟧ ⟶ L⟦s⟧)
    (hψ : ψ = f⟦s⟧') :
    δ (-1) 0 (s.negOnePow • (mappingCone.inl f).shift s) =
      Cochain.ofHom (ψ ≫ (mappingCone.inr f)⟦s⟧') := by
  subst ψ
  ext p
  dsimp
  simp only [Int.reduceNeg, δ_units_smul, Cochain.δ_shift, mappingCone.δ_inl,
    Cochain.ofHom_comp, smul_smul, Int.units_mul_self, one_smul, Cochain.shift_v',
    Cochain.comp_zero_cochain_v, Cochain.ofHom_v, shiftFunctor_obj_X', shiftFunctor_map_f']


lemma complexConeShift_inr (f : K ⟶ L) (s : ℤ) (ψ : K⟦s⟧ ⟶ L⟦s⟧)
    (hψ : ψ = f⟦s⟧') :
    (s.negOnePow • (mappingCone.inr f)⟦s⟧') ≫ (complexConeShiftIso f s ψ hψ).hom =
      (s.negOnePow • 𝟙 (L⟦s⟧)) ≫ mappingCone.inr ψ := by
  subst ψ
  exact (mappingCone.shiftTriangleIso f s).hom.comm₂

lemma complexConeShift_connecting (f : K ⟶ L) (s : ℤ) (ψ : K⟦s⟧ ⟶ L⟦s⟧)
    (hψ : ψ = f⟦s⟧') :
    (s.negOnePow • (mappingCone.triangle f).mor₃⟦s⟧') ≫
      (shiftFunctorComm (Complex A) 1 s).hom.app K =
        (complexConeShiftIso f s ψ hψ).hom ≫ (mappingCone.triangle ψ).mor₃ := by
  subst ψ
  let γ : (mappingCone f)⟦s⟧ ⟶ (K⟦(1 : ℤ)⟧)⟦s⟧ := (mappingCone.triangle f).mor₃⟦s⟧'
  let c : (K⟦(1 : ℤ)⟧)⟦s⟧ ⟶ (K⟦s⟧)⟦(1 : ℤ)⟧ :=
    (shiftFunctorComm (Complex A) 1 s).hom.app K
  let γ' : mappingCone (f⟦s⟧') ⟶ (K⟦s⟧)⟦(1 : ℤ)⟧ := (mappingCone.triangle (f⟦s⟧')).mor₃
  have h := (mappingCone.shiftTriangleIso f s).hom.comm₃
  dsimp only [mappingCone.shiftTriangleIso, Pretriangulated.Triangle.isoMk,
    Pretriangulated.Triangle.homMk, Pretriangulated.Triangle.shiftFunctor] at h
  change (s.negOnePow • (γ ≫ c)) ≫ (𝟙 (K⟦s⟧))⟦(1 : ℤ)⟧' =
    (mappingCone.shiftIso f s).hom ≫ γ' at h
  rw [(CategoryTheory.shiftFunctor (Complex A) (1 : ℤ)).map_id (K⟦s⟧), Category.comp_id] at h
  exact (Linear.units_smul_comp s.negOnePow γ c).trans h

end SerrePositivity.DifferentialGraded
end

end ConeShift

/-! ## ConeRotation（旧 SerrePositivity/DifferentialGraded/Complexes/ConeRotation.lean） -/

/-! # 包含と等しい射を用いるMathlibのcone回転比較

加群射の評価は包含と命題的に等しいため、その等式を明示的な引数にする。
-/

@[expose] public section ConeRotation
universe u

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits HomologicalComplex CochainComplex HomComplex
variable {A : Type u} [CommRing A] {K L : Complex A}

def complexConeRotationHom (f : K ⟶ L) (ψ : L ⟶ mappingCone f) (hψ : ψ = mappingCone.inr f) :
    K⟦(1 : ℤ)⟧ ⟶ mappingCone ψ := by
  subst ψ
  exact (mappingCone.rotateHomotopyEquiv f).hom

def complexConeRotationInv (f : K ⟶ L) (ψ : L ⟶ mappingCone f) (hψ : ψ = mappingCone.inr f) :
    mappingCone ψ ⟶ K⟦(1 : ℤ)⟧ := by
  subst ψ
  exact (mappingCone.rotateHomotopyEquiv f).inv

lemma complexConeRotationHom_cochain (f : K ⟶ L) (ψ : L ⟶ mappingCone f)
    (hψ : ψ = mappingCone.inr f) :
    Cochain.ofHom (complexConeRotationHom f ψ hψ) =
      mappingCone.liftCochain ψ (-(Cochain.ofHom f).leftShift 1 1 (zero_add 1))
        (-(mappingCone.inl f).leftShift 1 0 (neg_add_cancel 1)) (zero_add 1) := by
  subst ψ
  simp only [complexConeRotationHom, mappingCone.rotateHomotopyEquiv, mappingCone.ofHom_lift,
    Cocycle.coe_neg, Cocycle.leftShift_coe, Cocycle.ofHom_coe]

lemma complexConeRotationInv_cochain (f : K ⟶ L) (ψ : L ⟶ mappingCone f)
    (hψ : ψ = mappingCone.inr f) :
    Cochain.ofHom (complexConeRotationInv f ψ hψ) =
      mappingCone.descCochain ψ 0 (Cochain.ofHom (mappingCone.triangle f).mor₃)
        (neg_add_cancel 1) := by
  subst ψ
  simp only [complexConeRotationInv, mappingCone.rotateHomotopyEquiv, mappingCone.ofHom_desc]

lemma complexConeRotation_hom_inv (f : K ⟶ L) (ψ : L ⟶ mappingCone f)
    (hψ : ψ = mappingCone.inr f) :
    complexConeRotationHom f ψ hψ ≫ complexConeRotationInv f ψ hψ = 𝟙 _ := by
  subst ψ
  apply HomologicalComplex.Hom.ext
  funext n
  let H := (mappingCone.rotateHomotopyEquiv f).homotopyHomInvId
  have hzero (i j : ℤ) : H.hom i j = 0 := rfl
  have hc := H.comm n
  have hdn : dNext (C := K⟦(1 : ℤ)⟧) (D := K⟦(1 : ℤ)⟧) n H.hom = 0 := by
    change _ ≫ H.hom ((ComplexShape.up ℤ).next n) n = 0
    rw [hzero, comp_zero]
  have hpd : prevD (C := K⟦(1 : ℤ)⟧) (D := K⟦(1 : ℤ)⟧) n H.hom = 0 := by
    change H.hom n ((ComplexShape.up ℤ).prev n) ≫ _ = 0
    rw [hzero, zero_comp]
  rw [hdn, hpd, zero_add, zero_add] at hc
  exact hc

lemma complexConeRotation_inv_hom_boundary (f : K ⟶ L) (ψ : L ⟶ mappingCone f)
    (hψ : ψ = mappingCone.inr f) :
    δ (-1) 0 (-(mappingCone.snd ψ).comp
      ((mappingCone.snd f).comp (mappingCone.inl ψ) (zero_add (-1))) (zero_add (-1))) =
      Cochain.ofHom (complexConeRotationInv f ψ hψ ≫ complexConeRotationHom f ψ hψ) -
        Cochain.ofHom (𝟙 (mappingCone ψ)) := by
  subst ψ
  let H := (mappingCone.rotateHomotopyEquiv f).homotopyInvHomId
  have hc : ((Cochain.equivHomotopy _ _) H).val =
      -(mappingCone.snd (mappingCone.inr f)).comp
        ((mappingCone.snd f).comp (mappingCone.inl (mappingCone.inr f)) (zero_add (-1)))
        (zero_add (-1)) := by
    simp only [H, mappingCone.rotateHomotopyEquiv, Equiv.apply_symm_apply]
  have hd := ((Cochain.equivHomotopy _ _) H).property
  rw [hc] at hd
  exact (eq_sub_iff_add_eq).2 hd.symm

lemma complexConeRotation_connecting_boundary (f : K ⟶ L) (ψ : L ⟶ mappingCone f)
    (hψ : ψ = mappingCone.inr f) :
    δ (-1) 0 (-(mappingCone.snd f).comp (mappingCone.inl ψ) (zero_add (-1))) =
      (show Cochain (mappingCone f) (mappingCone ψ) 0 from
        Cochain.ofHom ((mappingCone.triangle f).mor₃ ≫ complexConeRotationHom f ψ hψ)) -
          Cochain.ofHom (mappingCone.inr ψ) := by
  subst ψ
  let H := mappingCone.rotateHomotopyEquivComm₂Homotopy f
  have hc : ((Cochain.equivHomotopy _ _) H).val =
      -(mappingCone.snd f).comp (mappingCone.inl (mappingCone.inr f)) (zero_add (-1)) := by
    simp only [H, mappingCone.rotateHomotopyEquivComm₂Homotopy, Equiv.apply_symm_apply]
  have hd := ((Cochain.equivHomotopy _ _) H).property
  rw [hc] at hd
  exact (eq_sub_iff_add_eq).2 hd.symm

lemma complexConeRotation_connecting (f : K ⟶ L) (ψ : L ⟶ mappingCone f)
    (hψ : ψ = mappingCone.inr f) :
    complexConeRotationHom f ψ hψ ≫ (mappingCone.triangle ψ).mor₃ = -f⟦(1 : ℤ)⟧' := by
  subst ψ
  exact mappingCone.rotateHomotopyEquiv_comm₃ f

end SerrePositivity.DifferentialGraded
end

end ConeRotation

/-! ## ConeElements（旧 SerrePositivity/DifferentialGraded/Complexes/ConeElements.lean） -/

/-! # module複体のconeの各次数の要素と二つの射影 -/

@[expose] public section ConeElements
universe u

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] {M N : Complex A}

def complexConeElementMk (f : M ⟶ N) (q : ℤ) (a : M.X (q + 1)) (b : N.X q) :
    (mappingCone f).X q :=
  (mappingCone.inl f).v (q + 1) q (by omega) a + (mappingCone.inr f).f q b

lemma complexConeElementMk_fst (f : M ⟶ N) (q : ℤ) (a : M.X (q + 1)) (b : N.X q) :
    (mappingCone.fst f).val.v q (q + 1) rfl (complexConeElementMk A f q a b) = a := by
  rw [complexConeElementMk, map_add, ← ModuleCat.comp_apply, mappingCone.inl_v_fst_v,
    ModuleCat.id_apply, ← ModuleCat.comp_apply, mappingCone.inr_f_fst_v]
  simp

lemma complexConeElementMk_snd (f : M ⟶ N) (q : ℤ) (a : M.X (q + 1)) (b : N.X q) :
    (mappingCone.snd f).v q q (add_zero q) (complexConeElementMk A f q a b) = b := by
  rw [complexConeElementMk, map_add, ← ModuleCat.comp_apply, mappingCone.inl_v_snd_v,
    ← ModuleCat.comp_apply, mappingCone.inr_f_snd_v, ModuleCat.id_apply]
  simp

lemma complexConeElement_ext (f : M ⟶ N) (q : ℤ) {z w : (mappingCone f).X q}
    (hfst : (mappingCone.fst f).val.v q (q + 1) rfl z =
      (mappingCone.fst f).val.v q (q + 1) rfl w)
    (hsnd : (mappingCone.snd f).v q q (add_zero q) z =
      (mappingCone.snd f).v q q (add_zero q) w) : z = w := by
  have hm : moduleElementMap A _ z = moduleElementMap A _ w := by
    apply mappingCone.ext_to f q (q + 1) rfl
    · apply (moduleElementEquiv A _).injective
      change (mappingCone.fst f).val.v q (q + 1) rfl ((1 : A) • z) =
        (mappingCone.fst f).val.v q (q + 1) rfl ((1 : A) • w)
      simpa only [one_smul] using hfst
    · apply (moduleElementEquiv A _).injective
      change (mappingCone.snd f).v q q (add_zero q) ((1 : A) • z) =
        (mappingCone.snd f).v q q (add_zero q) ((1 : A) • w)
      simpa only [one_smul] using hsnd
  have he := congrArg (fun a => a (1 : A)) hm
  change (1 : A) • z = (1 : A) • w at he
  simpa only [one_smul] using he

lemma complexConeElementMk_eta (f : M ⟶ N) (q : ℤ) (z : (mappingCone f).X q) :
    complexConeElementMk A f q ((mappingCone.fst f).val.v q (q + 1) rfl z)
      ((mappingCone.snd f).v q q (add_zero q) z) = z := by
  apply complexConeElement_ext A f q
  · exact complexConeElementMk_fst A f q _ _
  · exact complexConeElementMk_snd A f q _ _

end SerrePositivity.DifferentialGraded
end

end ConeElements

/-! ## ConeGradedSplit（旧 SerrePositivity/DifferentialGraded/Complexes/ConeGradedSplit.lean） -/

/-! # coneの次数付き分裂と全次数作用

左包含はchain mapとは限らないが、shiftの符号を含めた次数付き作用と可換する。
-/

@[expose] public section ConeGradedSplit
universe u

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits HomologicalComplex CochainComplex HomComplex
variable {A : Type u} [CommRing A] {P Q R S : Complex A}

lemma coneMapCochain_snd_v (f : P ⟶ Q) (g : R ⟶ S) {p : ℤ}
    (a : Homogeneous P R p) (b : Homogeneous Q S p)
    (i j : ℤ) (hij : i + p = j) :
    (coneMapCochain f g a b).v i j hij ≫ (mappingCone.snd g).v j j (add_zero j) =
      (mappingCone.snd f).v i i (add_zero i) ≫ b.v i j hij := by
  have h := Cochain.congr_v (coneMapCochain_snd f g a b) i j hij
  simpa only [Cochain.comp_zero_cochain_v, Cochain.zero_cochain_comp_v] using h

lemma coneMapCochain_inl_v (f : P ⟶ Q) (g : R ⟶ S) {p : ℤ}
    (a : Homogeneous P R p) (b : Homogeneous Q S p)
    (i j : ℤ) (hij : i + p = j) :
    (mappingCone.inl f).v (i + 1) i (by omega) ≫ (coneMapCochain f g a b).v i j hij =
      p.negOnePow • (a.v (i + 1) (j + 1) (by omega) ≫
        (mappingCone.inl g).v (j + 1) j (by omega)) := by
  rw [coneMapCochain_v]
  simp only [Preadditive.comp_add, Linear.comp_units_smul,
    mappingCone.inl_v_fst_v_assoc, mappingCone.inl_v_snd_v_assoc,
    zero_comp, add_zero]

/-- connecting mapの符号に合わせた、次数付き左section。 -/
def complexConeGradedSection (f : P ⟶ Q) (n : ℤ) :
    (P⟦(1 : ℤ)⟧).X n ⟶ (mappingCone f).X n :=
  -(mappingCone.inl f).v (n + 1) n (by omega)

/-- coneの右成分への次数付きretraction。 -/
def complexConeGradedRetraction (f : P ⟶ Q) (n : ℤ) :
    (mappingCone f).X n ⟶ Q.X n :=
  (mappingCone.snd f).v n n (add_zero n)

def complexConeGradedProjection (f : P ⟶ Q) (n : ℤ) :
    (mappingCone f).X n ⟶ (P⟦(1 : ℤ)⟧).X n :=
  -(mappingCone.fst f).val.v n (n + 1) rfl

lemma complexConeGradedProjection_eq_connecting (f : P ⟶ Q) (n : ℤ) :
    (mappingCone.triangle f).mor₃.f n = complexConeGradedProjection f n := by
  simp only [complexConeGradedProjection, SerrePositivity.coneTriangle_mor₃_f,
    CochainComplex.shiftFunctorObjXIso, HomologicalComplex.XIsoOfEq_rfl,
    Iso.refl_inv, Category.comp_id]

lemma complexConeGradedSection_connecting (f : P ⟶ Q) (n : ℤ) :
    complexConeGradedSection f n ≫ complexConeGradedProjection f n = 𝟙 _ := by
  simp only [complexConeGradedSection, complexConeGradedProjection,
    Preadditive.neg_comp, Preadditive.comp_neg,
    neg_neg, mappingCone.inl_v_fst_v]
  rfl

lemma complexConeGradedRetraction_inr (f : P ⟶ Q) (n : ℤ) :
    (mappingCone.inr f).f n ≫ complexConeGradedRetraction f n = 𝟙 _ :=
  mappingCone.inr_f_snd_v f n

lemma complexConeGradedSection_retraction (f : P ⟶ Q) (n : ℤ) :
    complexConeGradedSection f n ≫ complexConeGradedRetraction f n = 0 := by
  simp only [complexConeGradedSection, complexConeGradedRetraction,
    Preadditive.neg_comp, mappingCone.inl_v_snd_v, neg_zero]

lemma complexConeGraded_decomposition (f : P ⟶ Q) (n : ℤ) :
    complexConeGradedRetraction f n ≫ (mappingCone.inr f).f n +
      complexConeGradedProjection f n ≫ complexConeGradedSection f n = 𝟙 _ := by
  simp only [complexConeGradedSection, complexConeGradedRetraction,
    complexConeGradedProjection,
    Preadditive.neg_comp, Preadditive.comp_neg, neg_neg]
  exact (add_comm _ _).trans (mappingCone.id_X f n (n + 1) rfl)

lemma complexConeGradedSection_naturality (f : P ⟶ Q) (g : R ⟶ S) {p : ℤ}
    (a : Homogeneous P R p) (b : Homogeneous Q S p)
    (i j : ℤ) (hij : i + p = j) :
    complexConeGradedSection f i ≫ (coneMapCochain f g a b).v i j hij =
      ((shiftHom 1 P R).f p a).v i j hij ≫ complexConeGradedSection g j := by
  simp only [complexConeGradedSection, Preadditive.neg_comp, Preadditive.comp_neg]
  congr 1
  rw [coneMapCochain_inl_v]
  rw [shiftHom_v]
  simp only [one_mul, Linear.units_smul_comp]

end SerrePositivity.DifferentialGraded
end

end ConeGradedSplit

/-! ## ConeComposition（旧 SerrePositivity/DifferentialGraded/Complexes/ConeComposition.lean） -/

/-! # 指定された合成とcone射に対する八面体の複体比較

加群の評価は合成とcone射に命題的に一致する。その等式を入力に保持する。
-/

@[expose] public section ConeComposition
universe u

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory HomologicalComplex CochainComplex HomComplex
variable {A : Type u} [CommRing A] {K L P : Complex A}

/-- cone(g)と、指定されたcone(f)→cone(θ)のconeとの既存ホモトピー同値。 -/
def complexConeCompHomotopyEquiv (f : K ⟶ L) (g : L ⟶ P) (θ : K ⟶ P)
    (hθ : θ = f ≫ g) (χ : mappingCone f ⟶ mappingCone θ)
    (hχ : χ = mappingCone.map f θ (𝟙 K) g (by rw [hθ, Category.id_comp])) :
    HomotopyEquiv (mappingCone g) (mappingCone χ) := by
  subst θ
  subst χ
  exact mappingConeCompHomotopyEquiv f g

lemma complexConeComp_hom_cochain (f : K ⟶ L) (g : L ⟶ P) (θ : K ⟶ P)
    (hθ : θ = f ≫ g) (χ : mappingCone f ⟶ mappingCone θ)
    (hχ : χ = mappingCone.map f θ (𝟙 K) g (by rw [hθ, Category.id_comp])) :
    Cochain.ofHom (complexConeCompHomotopyEquiv f g θ hθ χ hχ).hom =
      mappingCone.liftCochain χ
        ((mappingCone.fst g).val.comp (Cochain.ofHom (mappingCone.inr f)) (add_zero 1))
        (mappingCone.descCochain g 0 (Cochain.ofHom (mappingCone.inr θ)) (neg_add_cancel 1))
        (zero_add 1) := by
  subst θ
  subst χ
  simp only [complexConeCompHomotopyEquiv, mappingConeCompHomotopyEquiv,
    MappingConeCompHomotopyEquiv.hom, mappingConeCompTriangle, Pretriangulated.Triangle.mk,
    mappingCone.ofHom_lift, mappingCone.descCocycle_coe,
    mappingCone.descCochain, Cocycle.coe_zero, Cochain.comp_zero, add_zero]

lemma complexConeComp_inv_cochain (f : K ⟶ L) (g : L ⟶ P) (θ : K ⟶ P)
    (hθ : θ = f ≫ g) (χ : mappingCone f ⟶ mappingCone θ)
    (hχ : χ = mappingCone.map f θ (𝟙 K) g (by rw [hθ, Category.id_comp])) :
    Cochain.ofHom (complexConeCompHomotopyEquiv f g θ hθ χ hχ).inv =
      mappingCone.descCochain χ ((mappingCone.snd f).comp (mappingCone.inl g) (zero_add (-1)))
        (mappingCone.descCochain θ ((Cochain.ofHom f).comp (mappingCone.inl g) (zero_add (-1)))
          (Cochain.ofHom (mappingCone.inr g)) (neg_add_cancel 1)) (neg_add_cancel 1) := by
  subst θ
  subst χ
  simp only [complexConeCompHomotopyEquiv, mappingConeCompHomotopyEquiv,
    MappingConeCompHomotopyEquiv.inv, mappingConeCompTriangle, Pretriangulated.Triangle.mk,
    mappingCone.ofHom_desc]

lemma complexConeComp_hom_inv (f : K ⟶ L) (g : L ⟶ P) (θ : K ⟶ P)
    (hθ : θ = f ≫ g) (χ : mappingCone f ⟶ mappingCone θ)
    (hχ : χ = mappingCone.map f θ (𝟙 K) g (by rw [hθ, Category.id_comp])) :
    (complexConeCompHomotopyEquiv f g θ hθ χ hχ).hom ≫
      (complexConeCompHomotopyEquiv f g θ hθ χ hχ).inv = 𝟙 _ := by
  subst θ
  subst χ
  exact mappingConeCompHomotopyEquiv_hom_inv_id f g

lemma complexConeComp_inv_hom_boundary (f : K ⟶ L) (g : L ⟶ P) (θ : K ⟶ P)
    (hθ : θ = f ≫ g) (χ : mappingCone f ⟶ mappingCone θ)
    (hχ : χ = mappingCone.map f θ (𝟙 K) g (by rw [hθ, Category.id_comp])) :
    δ (-1) 0 (-((mappingCone.snd χ).comp ((mappingCone.fst θ).val.comp
      ((mappingCone.inl f).comp (mappingCone.inl χ) (by decide))
        (show (1 : ℤ) + (-2) = -1 by decide)) (zero_add (-1)))) =
      Cochain.ofHom ((complexConeCompHomotopyEquiv f g θ hθ χ hχ).inv ≫
        (complexConeCompHomotopyEquiv f g θ hθ χ hχ).hom) - Cochain.ofHom (𝟙 _) := by
  subst θ
  subst χ
  let H := (mappingConeCompHomotopyEquiv f g).homotopyInvHomId
  have hc : ((Cochain.equivHomotopy _ _) H).val =
      -((mappingCone.snd _).comp ((mappingCone.fst (f ≫ g)).val.comp
        ((mappingCone.inl f).comp (mappingCone.inl _) (by decide))
          (show (1 : ℤ) + (-2) = -1 by decide)) (zero_add (-1))) := by
    simp only [H, mappingConeCompHomotopyEquiv, MappingConeCompHomotopyEquiv.homotopyInvHomId,
      Equiv.apply_symm_apply]
  have hd := ((Cochain.equivHomotopy _ _) H).property
  rw [hc] at hd
  exact (eq_sub_iff_add_eq).2 hd.symm

lemma complexConeComp_inr_inv (f : K ⟶ L) (g : L ⟶ P) (θ : K ⟶ P)
    (hθ : θ = f ≫ g) (χ : mappingCone f ⟶ mappingCone θ)
    (hχ : χ = mappingCone.map f θ (𝟙 K) g (by rw [hθ, Category.id_comp])) :
    mappingCone.inr χ ≫ (complexConeCompHomotopyEquiv f g θ hθ χ hχ).inv =
      mappingCone.map θ g f (𝟙 P) (by rw [hθ, Category.comp_id]) := by
  subst θ
  subst χ
  exact mappingConeCompHomotopyEquiv_comm₁ f g

lemma complexConeComp_hom_connecting (f : K ⟶ L) (g : L ⟶ P) (θ : K ⟶ P)
    (hθ : θ = f ≫ g) (χ : mappingCone f ⟶ mappingCone θ)
    (hχ : χ = mappingCone.map f θ (𝟙 K) g (by rw [hθ, Category.id_comp])) :
    (complexConeCompHomotopyEquiv f g θ hθ χ hχ).hom ≫ (mappingCone.triangle χ).mor₃ =
      (mappingCone.triangle g).mor₃ ≫ (mappingCone.inr f)⟦(1 : ℤ)⟧' := by
  subst θ
  subst χ
  exact mappingConeCompHomotopyEquiv_comm₂ f g

lemma complexConeComp_inputs_cycle (f : K ⟶ L) (g : L ⟶ P) (θ : K ⟶ P)
    (hθ : θ = f ≫ g) (χ : mappingCone f ⟶ mappingCone θ)
    (hχ : χ = mappingCone.map f θ (𝟙 K) g (by rw [hθ, Category.id_comp])) :
    δ 0 1 (mappingCone.descCochain g 0 (Cochain.ofHom (mappingCone.inr θ))
      (neg_add_cancel 1)) +
        ((mappingCone.fst g).val.comp (Cochain.ofHom (mappingCone.inr f)) (add_zero 1)).comp
          (Cochain.ofHom χ) (add_zero 1) = 0 := by
  subst θ
  subst χ
  apply Cochain.ext
  intro p q hpq
  subst q
  dsimp [mappingCone.map]
  simp [mappingCone.ext_from_iff _ _ _ rfl,
    mappingCone.inl_v_d_assoc _ (p + 1) p (p + 2) (by omega) (by omega)]

end SerrePositivity.DifferentialGraded
end

end ConeComposition

/-! ## ConeCompositionDesc（旧 SerrePositivity/DifferentialGraded/Complexes/ConeCompositionDesc.lean） -/

/-! # 合成coneの逆方向比較に用いるdescの境界式 -/

@[expose] public section ConeCompositionDesc
universe u

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory HomologicalComplex CochainComplex HomComplex
variable {A : Type u} [CommRing A] {K L P : Complex A}

lemma complexConeComp_inner_boundary (f : K ⟶ L) (g : L ⟶ P) (θ : K ⟶ P)
    (hθ : θ = f ≫ g) :
    δ (-1) 0 ((Cochain.ofHom f).comp (mappingCone.inl g) (zero_add (-1))) =
      Cochain.ofHom (θ ≫ mappingCone.inr g) := by
  subst θ
  rw [δ_ofHom_comp, mappingCone.δ_inl, ← Cochain.ofHom_comp, Category.assoc]

lemma complexConeComp_outer_boundary (f : K ⟶ L) (g : L ⟶ P) (θ : K ⟶ P)
    (hθ : θ = f ≫ g) (χ : mappingCone f ⟶ mappingCone θ)
    (hχ : χ = mappingCone.map f θ (𝟙 K) g (by rw [hθ, Category.id_comp])) :
    δ (-1) 0 ((mappingCone.snd f).comp (mappingCone.inl g) (zero_add (-1))) =
      Cochain.ofHom (χ ≫ mappingCone.desc θ
        ((Cochain.ofHom f).comp (mappingCone.inl g) (zero_add (-1))) (mappingCone.inr g)
        (complexConeComp_inner_boundary f g θ hθ)) := by
  subst θ
  subst χ
  apply Cochain.ext₀
  intro p
  rw [mappingCone.ext_from_iff _ (p + 1) p rfl,
    mappingCone.ext_to_iff _ _ (p + 1) rfl]
  simp [mappingCone.map, δ_zero_cochain_comp,
    Cochain.comp_v _ _ (add_neg_cancel 1) p (p + 1) p (by omega) (by omega)]

end SerrePositivity.DifferentialGraded
end

end ConeCompositionDesc

/-! ## ConeRepresentation（旧 SerrePositivity/DifferentialGraded/Complexes/ConeRepresentation.lean） -/

/-! # 四つの包含・射影からの標準cone比較の可逆性 -/

@[expose] public section ConeRepresentation
universe u

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] {X Y K : Complex A}
variable (f : X ⟶ Y) (α : Cochain X K (-1)) (β : Y ⟶ K)
  (γ : Cochain K X 1) (η : Cochain K Y 0)
  (hδ : δ (-1) 0 α = Cochain.ofHom (f ≫ β))

def complexConeDescInverseElement (n : ℤ) (z : K.X n) : (mappingCone f).X n :=
  complexConeElementMk A f n (γ.v n (n + 1) rfl z) (η.v n n (add_zero n) z)

lemma complexConeDesc_fst
    (hαγ : α.comp γ (neg_add_cancel 1) = Cochain.ofHom (𝟙 X))
    (hβγ : (Cochain.ofHom β).comp γ (zero_add 1) = 0) (n : ℤ) :
    (mappingCone.desc f α β hδ).f n ≫ γ.v n (n + 1) rfl =
      (mappingCone.fst f).val.v n (n + 1) rfl := by
  apply mappingCone.ext_from f (n + 1) n rfl
  · rw [← Category.assoc, mappingCone.inl_v_desc_f, mappingCone.inl_v_fst_v]
    have h := Cochain.congr_v hαγ (n + 1) (n + 1) (add_zero (n + 1))
    rw [Cochain.comp_v _ _ _ (n + 1) n (n + 1) (by omega) rfl,
      Cochain.ofHom_v, HomologicalComplex.id_f] at h
    exact h
  · rw [← Category.assoc, mappingCone.inr_f_desc_f, mappingCone.inr_f_fst_v]
    have h := Cochain.congr_v hβγ n (n + 1) rfl
    simpa only [Cochain.zero_cochain_comp_v, Cochain.ofHom_v, Cochain.zero_v] using h

lemma complexConeDesc_snd
    (hαη : α.comp η (add_zero (-1)) = 0)
    (hβη : (Cochain.ofHom β).comp η (zero_add 0) = Cochain.ofHom (𝟙 Y)) (n : ℤ) :
    (mappingCone.desc f α β hδ).f n ≫ η.v n n (add_zero n) =
      (mappingCone.snd f).v n n (add_zero n) := by
  apply mappingCone.ext_from f (n + 1) n rfl
  · rw [← Category.assoc, mappingCone.inl_v_desc_f, mappingCone.inl_v_snd_v]
    have h := Cochain.congr_v hαη (n + 1) n (by omega)
    simpa only [Cochain.comp_zero_cochain_v, Cochain.zero_v] using h
  · rw [← Category.assoc, mappingCone.inr_f_desc_f, mappingCone.inr_f_snd_v]
    have h := Cochain.congr_v hβη n n (add_zero n)
    simpa only [Cochain.comp_zero_cochain_v, Cochain.ofHom_v, HomologicalComplex.id_f] using h

lemma complexConeDesc_rightInverse
    (hd : γ.comp α (add_neg_cancel 1) + η.comp (Cochain.ofHom β) (add_zero 0) =
      Cochain.ofHom (𝟙 K)) (n : ℤ) :
    Function.RightInverse (complexConeDescInverseElement A f γ η n)
      ((mappingCone.desc f α β hδ).f n) := by
  intro z
  have h := Cochain.congr_v hd n n (add_zero n)
  rw [Cochain.add_v, Cochain.comp_v _ _ _ n (n + 1) n rfl (by omega),
    Cochain.comp_zero_cochain_v] at h
  simp only [Cochain.ofHom_v, HomologicalComplex.id_f] at h
  have hz := congrArg (fun p => p z) h
  simp only [ModuleCat.hom_add, LinearMap.add_apply, ModuleCat.comp_apply, ModuleCat.id_apply] at hz
  rw [complexConeDescInverseElement, complexConeElementMk, map_add]
  change ((mappingCone.inl f).v (n + 1) n (by omega) ≫ (mappingCone.desc f α β hδ).f n)
      (γ.v n (n + 1) rfl z) +
    ((mappingCone.inr f).f n ≫ (mappingCone.desc f α β hδ).f n) (η.v n n (add_zero n) z) = z
  rw [mappingCone.inl_v_desc_f, mappingCone.inr_f_desc_f]
  exact hz

lemma complexConeDesc_leftInverse
    (hαγ : α.comp γ (neg_add_cancel 1) = Cochain.ofHom (𝟙 X))
    (hαη : α.comp η (add_zero (-1)) = 0)
    (hβγ : (Cochain.ofHom β).comp γ (zero_add 1) = 0)
    (hβη : (Cochain.ofHom β).comp η (zero_add 0) = Cochain.ofHom (𝟙 Y)) (n : ℤ) :
    Function.LeftInverse (complexConeDescInverseElement A f γ η n)
      ((mappingCone.desc f α β hδ).f n) := by
  intro z
  apply complexConeElement_ext A f n
  · rw [complexConeDescInverseElement, complexConeElementMk_fst,
      ← ModuleCat.comp_apply, complexConeDesc_fst A f α β γ hδ hαγ hβγ n]
  · rw [complexConeDescInverseElement, complexConeElementMk_snd,
      ← ModuleCat.comp_apply, complexConeDesc_snd A f α β η hδ hαη hβη n]

lemma complexConeDesc_bijective
    (hαγ : α.comp γ (neg_add_cancel 1) = Cochain.ofHom (𝟙 X))
    (hαη : α.comp η (add_zero (-1)) = 0)
    (hβγ : (Cochain.ofHom β).comp γ (zero_add 1) = 0)
    (hβη : (Cochain.ofHom β).comp η (zero_add 0) = Cochain.ofHom (𝟙 Y))
    (hd : γ.comp α (add_neg_cancel 1) + η.comp (Cochain.ofHom β) (add_zero 0) =
      Cochain.ofHom (𝟙 K)) (n : ℤ) : Function.Bijective ((mappingCone.desc f α β hδ).f n) :=
  ⟨(complexConeDesc_leftInverse A f α β γ η hδ hαγ hαη hβγ hβη n).injective,
    (complexConeDesc_rightInverse A f α β γ η hδ hd n).surjective⟩

lemma complexConeDesc_isIso
    (hαγ : α.comp γ (neg_add_cancel 1) = Cochain.ofHom (𝟙 X))
    (hαη : α.comp η (add_zero (-1)) = 0)
    (hβγ : (Cochain.ofHom β).comp γ (zero_add 1) = 0)
    (hβη : (Cochain.ofHom β).comp η (zero_add 0) = Cochain.ofHom (𝟙 Y))
    (hd : γ.comp α (add_neg_cancel 1) + η.comp (Cochain.ofHom β) (add_zero 0) =
      Cochain.ofHom (𝟙 K)) : IsIso (mappingCone.desc f α β hδ) := by
  let (n : ℤ) : IsIso ((mappingCone.desc f α β hδ).f n) :=
    (ConcreteCategory.isIso_iff_bijective _).2
      (complexConeDesc_bijective A f α β γ η hδ hαγ hαη hβγ hβη hd n)
  exact HomologicalComplex.Hom.isIso_of_components _

end SerrePositivity.DifferentialGraded
end

end ConeRepresentation

/-! ## HomCovariant（旧 SerrePositivity/DifferentialGraded/Complexes/HomCovariant.lean） -/

/-! # 固定始域からの共変Hom dg関手 -/

@[expose] public section HomCovariant
universe u

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory CochainComplex HomComplex
variable (A : Type u) [CommRing A]

/-- Ch(A)の左representableを使う共変Hom関手。 -/
def homCovariantDG (P : Complex A) : DGFunctor A (Complex A) (Complex A) :=
  leftRepresentable A P

/-- 共変Homの作用は通常順の後合成であり、追加のKoszul符号は付かない。 -/
lemma homCovariantDG_map_element (P T T' : Complex A) (p q n : ℤ) (hn : q + p = n)
    (f : Homogeneous T T' p) (g : Homogeneous P T q) :
    (((homCovariantDG A P).map T T').f p f).v q n hn g = g.comp f hn := by
  change leftAction A (leftRepresentable A P) f g hn = _
  rw [leftRepresentable_action]
  change (p * q).negOnePow • forward A (D := Complex A) g f hn = _
  change (p * q).negOnePow • (enrichedComposition P T T').f n
    (HomologicalComplex.ιTensorObj (homComplex A P T) (homComplex A T T') q p n hn
      (g ⊗ₜ[A] f)) = _
  rw [enrichedComposition_apply, smul_smul, mul_comm q p, Int.units_mul_self, one_smul]

lemma homCovariantDG_closedMap (P : Complex A) {T T' : Complex A} (f : T ⟶ T') :
    closedMap A f ≫ (homCovariantDG A P).map T T' = closedMap A (homPostcompose P f) := by
  apply (unitCycleEquiv _).injective
  apply Subtype.ext
  change (cycleFromUnit _ (closedMap A f ≫ (homCovariantDG A P).map T T')).val =
    (cycleFromUnit _ (closedMap A (homPostcompose P f))).val
  rw [cycleFromUnit_postcomp, closedMap_cycle, closedMap_cycle]
  apply Cochain.ext₀
  intro r
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro g
  change (((homCovariantDG A P).map T T').f 0 (Cochain.ofHom f)).v r r (add_zero r) g =
    (homPostcompose P f).f r g
  rw [homCovariantDG_map_element]
  rfl

end SerrePositivity.DifferentialGraded
end

end HomCovariant

/-! ## HomContravariant（旧 SerrePositivity/DifferentialGraded/Complexes/HomContravariant.lean） -/

/-! # 固定終域への反変Hom dg関手 -/

@[expose] public section HomContravariant
universe u

noncomputable section
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Opposite CochainComplex HomComplex
variable (A : Type u) [CommRing A]

/-- Ch(A)上の代表右加群を再利用する。対象全体のsmallnessは要求しない。 -/
def homContravariantDG (T : Complex A) : DGFunctor A (Complex A)ᵒᵖ (Complex A) :=
  (representable A T).toFunctor

lemma homContravariantDG_obj (T : Complex A) (P : (Complex A)ᵒᵖ) :
    (homContravariantDG A T).obj P = homComplex A P.unop T := rfl

/-- 反変Homの全次数作用は符号付き前合成。 -/
lemma homContravariantDG_map_element (T : Complex A) (P Q : (Complex A)ᵒᵖ)
    (p q n : ℤ) (hn : q + p = n) (f : Homogeneous Q.unop P.unop p)
    (g : Homogeneous P.unop T q) :
    (((homContravariantDG A T).map P Q).f p f).v q n hn g =
      (p * q).negOnePow • f.comp g (by omega) := by
  change ((representableMap A T P Q).f p f).v q n hn g = _
  rw [representableMap_apply]
  exact enrichedComposition_apply Q.unop P.unop T p q n (by omega) f g

end SerrePositivity.DifferentialGraded
end

end HomContravariant

/-! ## HomContravariantMaps（旧 SerrePositivity/DifferentialGraded/Complexes/HomContravariantMaps.lean） -/

/-! # 反変Hom dg関手の閉零射での計算 -/

@[expose] public section HomContravariantMaps
universe u

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Opposite CochainComplex HomComplex
variable (A : Type u) [CommRing A]

lemma homContravariantDG_closedMap {P Q : Complex A} (f : P ⟶ Q) (T : Complex A) :
    closedMap A f ≫ (homContravariantDG A T).map (op Q) (op P) =
      closedMap A (homPrecompose f T) := by
  apply (unitCycleEquiv _).injective
  apply Subtype.ext
  change (cycleFromUnit _ (closedMap A f ≫ (homContravariantDG A T).map (op Q) (op P))).val =
    (cycleFromUnit _ (closedMap A (homPrecompose f T))).val
  rw [cycleFromUnit_postcomp, closedMap_cycle, closedMap_cycle]
  apply Cochain.ext₀
  intro r
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro g
  change (((homContravariantDG A T).map (op Q) (op P)).f 0 (Cochain.ofHom f)).v
      r r (add_zero r) g = (homPrecompose f T).f r g
  rw [homContravariantDG_map_element]
  simp only [zero_mul, Int.negOnePow_zero, one_smul]
  rfl

end SerrePositivity.DifferentialGraded
end

end HomContravariantMaps
