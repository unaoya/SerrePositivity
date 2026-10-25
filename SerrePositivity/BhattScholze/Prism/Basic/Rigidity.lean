module

public import SerrePositivity.BhattScholze.Prism.Basic.OrientedPrism
public import Mathlib.LinearAlgebra.TensorProduct.Lift
public import SerrePositivity.BhattScholze.Delta.Perfect.PerfectDelta
public import Mathlib.RingTheory.AdicCompletion.Functoriality
public import SerrePositivity.BhattScholze.Prism.Bounded.Completeness

/-!
# prism の射の剛性（BS 著者版 Lemma 3.5）

## 概要
prism の射で生成元は単元倍に写る、IB = J、I ⊗ B ≅ J。標的が p 正則・完全・有界の場合。商の射による同型判定。

## 方針
Lemma 2.24 を生成元に当てる。単元性に要る根基への所属を標的の古典的完備性から得る。

## 規約
仮定なしの一般形は未（ノート BR27）。

## 使われ方
完全 prism の比較、Thm 3.10、Lemma 4.8。
-/

universe u v

/-! ## p正則なoriented prism射の剛性（旧 Prism/Basic/OrientedPrismRegularRigidity.lean）

著者公開版Lemma 3.5の主イデアルの局所計算。
完全性を要求せず、pの正則性とprismの実導来完備性から古典的p完備性を得て使う。
pねじれのある一般prismやCartierイデアルの降下はこの定理の範囲外。
-/

@[expose] public noncomputable section OrientedPrismRegularRigidity

namespace SerrePositivity.BhattScholze.OrientedPrism.Hom
variable {p : ℕ} [Fact p.Prime] {A : Type u} {B : Type v} [CommRing A] [CommRing B]
variable {P : OrientedPrism p A} {Q : OrientedPrism p B}

/-- p正則なoriented prism射は、生成元を一意な単元係数で写す。 -/
theorem existsUnique_generator_unit_of_p_regular (f : Hom P Q)
    (hP : Function.Injective (fun x : A ↦ (p : A) * x))
    (hQ : Function.Injective (fun x : B ↦ (p : B) * x)) :
    ∃! u : Bˣ, f.toRingHom P.generator = Q.generator * u := by
  obtain ⟨r, hr⟩ := Ideal.mem_span_singleton.mp f.map_generator_mem
  have hdist := f.map_delta.map_isDistinguished (P.isDistinguished_of_p_regular hP)
  rw [hr] at hdist
  let := Q.isAdicComplete_generator
  let := Q.isAdicComplete_p_of_regular hQ
  have hru : IsUnit r :=
    (Q.deltaStructure.isDistinguished_factor Q.generator r hdist
      (IsAdicComplete.le_jacobson_bot (Ideal.span {Q.generator})
        (Ideal.subset_span (by simp)))
      (IsAdicComplete.le_jacobson_bot (Ideal.span {(p : B)})
        (Ideal.subset_span (by simp)))).2
  obtain ⟨u, hu⟩ := hru
  refine ⟨u, by simpa only [hu] using hr, ?_⟩
  intro v hv
  apply Units.ext
  apply Q.generator_regular
  change Q.generator * (v : B) = Q.generator * (u : B)
  exact hv.symm.trans (by simpa only [hu] using hr)

/-- p正則なoriented prism射のイデアル像は終域のprismイデアル全体。 -/
theorem map_ideal_eq_of_p_regular (f : Hom P Q)
    (hP : Function.Injective (fun x : A ↦ (p : A) * x))
    (hQ : Function.Injective (fun x : B ↦ (p : B) * x)) : P.ideal.map f.toRingHom = Q.ideal := by
  let := Q.isAdicComplete_generator
  let := Q.isAdicComplete_p_of_regular hQ
  exact f.map_delta.map_span_eq_of_distinguished_of_mem_span
    (P.isDistinguished_of_p_regular hP) f.map_generator_mem
    (IsAdicComplete.le_jacobson_bot (Ideal.span {Q.generator}) (Ideal.subset_span (by simp)))
    (IsAdicComplete.le_jacobson_bot (Ideal.span {(p : B)}) (Ideal.subset_span (by simp)))

/-- p正則なoriented prism射の生成元像は非零因子。 -/
theorem map_generator_mul_injective_of_p_regular (f : Hom P Q)
    (hP : Function.Injective (fun x : A ↦ (p : A) * x))
    (hQ : Function.Injective (fun x : B ↦ (p : B) * x)) :
    Function.Injective (fun x : B ↦ f.toRingHom P.generator * x) := by
  obtain ⟨u, hu, _⟩ := f.existsUnique_generator_unit_of_p_regular hP hQ
  intro x y hxy
  change f.toRingHom P.generator * x = f.toRingHom P.generator * y at hxy
  rw [hu, mul_assoc, mul_assoc] at hxy
  have h := Q.generator_regular hxy
  exact (IsUnit.isUnit_iff_mulLeft_bijective.mp u.isUnit).1 h

end SerrePositivity.BhattScholze.OrientedPrism.Hom

end OrientedPrismRegularRigidity

/-! ## 完全oriented prism射の生成元と商同型（旧 Prism/Basic/OrientedPrismHomRigidity.lean）

著者公開版Lemma 3.5の主イデアルの射について、生成元の像の一意な単元係数を
構成する。台の環射が同型なら標準商も同型となる。
-/

@[expose] public noncomputable section OrientedPrismHomRigidity

namespace SerrePositivity.BhattScholze.OrientedPrism.Hom
variable {p : ℕ} [Fact p.Prime] {A : Type u} {B : Type v} [CommRing A] [CommRing B]
variable {P : OrientedPrism p A} {Q : OrientedPrism p B}

/-- 完全oriented prism射は、源の生成元を終域の生成元の一意な単元倍へ送る。 -/
theorem existsUnique_generator_unit (f : Hom P Q)
    (hP : P.deltaStructure.IsPerfect) (hQ : Q.deltaStructure.IsPerfect) :
    ∃! u : Bˣ, f.toRingHom P.generator = Q.generator * u :=
  f.existsUnique_generator_unit_of_p_regular hP.p_mul_injective hQ.p_mul_injective

/-- 台環射が全単射の完全oriented prism射は、具体的な標準商同型を与える。 -/
def quotientEquiv (f : Hom P Q) (hP : P.deltaStructure.IsPerfect)
    (hQ : Q.deltaStructure.IsPerfect) (hf : Function.Bijective f.toRingHom) :
    A ⧸ P.ideal ≃+* B ⧸ Q.ideal :=
  Ideal.quotientEquiv P.ideal Q.ideal (RingEquiv.ofBijective f.toRingHom hf)
    (f.map_ideal_eq_of_perfect hP hQ).symm

/-- 構成した商同型は既存の誘導商射に一致する。 -/
@[simp] theorem quotientEquiv_toRingHom (f : Hom P Q) (hP : P.deltaStructure.IsPerfect)
    (hQ : Q.deltaStructure.IsPerfect) (hf : Function.Bijective f.toRingHom) :
    (f.quotientEquiv hP hQ hf).toRingHom = f.quotientMap := rfl

/-- 完全oriented prismの同型は商上でも全単射。 -/
theorem quotientMap_bijective (f : Hom P Q) (hP : P.deltaStructure.IsPerfect)
    (hQ : Q.deltaStructure.IsPerfect) (hf : Function.Bijective f.toRingHom) :
    Function.Bijective f.quotientMap := (f.quotientEquiv hP hQ hf).bijective

end SerrePositivity.BhattScholze.OrientedPrism.Hom

end OrientedPrismHomRigidity

/-! ## oriented prism射のイデアルのテンソル基底変換（旧 Prism/Basic/OrientedPrismIdealTensor.lean）

著者公開版Lemma 3.5の主イデアルの場合。標準的なB⊗A Iの順序で
自然な乗法写像を構成し、それがB線形同型であると証明する。
一般Cartierイデアルへの忠実平坦降下は含めない。
-/

@[expose] public noncomputable section OrientedPrismIdealTensor

open scoped TensorProduct
namespace SerrePositivity.BhattScholze.OrientedPrism
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]

/-- 選択した非零因子の生成元によるprismイデアルの具体的な自明化。 -/
def generatorLinearEquiv (P : OrientedPrism p A) : A ≃ₗ[A] P.ideal :=
  LinearEquiv.ofBijective
    ((LinearMap.mulLeft A P.generator).codRestrict P.ideal
      (fun r ↦ P.ideal.mul_mem_right r (Ideal.subset_span (Set.mem_singleton _))))
    ⟨fun _ _ h ↦ P.generator_regular (congrArg Subtype.val h), by
      intro x
      obtain ⟨r, hr⟩ := Ideal.mem_span_singleton.mp x.property
      exact ⟨r, Subtype.ext hr.symm⟩⟩

/-- prismイデアルの自明化は選択生成元の乗法。 -/
@[simp] theorem generatorLinearEquiv_apply (P : OrientedPrism p A) (r : A) :
    (P.generatorLinearEquiv r : A) = P.generator * r := rfl

namespace Hom
variable {B : Type v} [CommRing B]
variable {P : OrientedPrism p A} {Q : OrientedPrism p B}

section Compatible
variable [Algebra A B]

/-- prism射と両立するA代数構造に関して、イデアル上の標準A線形写像。 -/
def idealLinearMap (f : Hom P Q) (hf : f.toRingHom = algebraMap A B) : P.ideal →ₗ[A] Q.ideal where
  toFun x := ⟨f.toRingHom (x : A), f.ideal_le x.property⟩
  map_add' x y := Subtype.ext (map_add f.toRingHom (x : A) (y : A))
  map_smul' a x := by
    apply Subtype.ext
    simp [Algebra.smul_def, map_mul, hf]

/-- イデアルのテンソル基底変換の標準B線形写像。 -/
def idealTensorMap (f : Hom P Q) (hf : f.toRingHom = algebraMap A B) :
    B ⊗[A] P.ideal →ₗ[B] Q.ideal :=
  (f.idealLinearMap hf).liftBaseChange B

/-- 純テンソルの標準写像はb*f(x)。 -/
@[simp] theorem idealTensorMap_tmul (f : Hom P Q) (hf : f.toRingHom = algebraMap A B)
    (b : B) (x : P.ideal) :
    (f.idealTensorMap hf (b ⊗ₜ[A] x) : B) = b * f.toRingHom x := rfl

/-- 生成元像の単元係数から標準イデアル基底変換写像の全単射性を得る。 -/
theorem idealTensorMap_bijective_of_generator_unit (f : Hom P Q) (hf : f.toRingHom = algebraMap A B)
    (u : Bˣ) (hu : f.toRingHom P.generator = Q.generator * u) :
    Function.Bijective (f.idealTensorMap hf) := by
  let e₁ := (P.generatorLinearEquiv.symm.baseChange A B P.ideal A).trans
    (TensorProduct.AlgebraTensorModule.rid A B B)
  let e₂ := (LinearEquiv.smulOfUnit u : B ≃ₗ[B] B).trans Q.generatorLinearEquiv
  have he : f.idealTensorMap hf = (e₁.trans e₂).toLinearMap := by
    apply TensorProduct.AlgebraTensorModule.ext
    intro b x
    apply Subtype.ext
    let r := P.generatorLinearEquiv.symm x
    have hx : (x : A) = P.generator * r := by
      have h := congrArg Subtype.val (P.generatorLinearEquiv.apply_symm_apply x)
      exact h.symm
    change b * f.toRingHom (x : A) = Q.generator * ((u : B) * (r • b))
    rw [hx, map_mul, hu, hf]
    rw [Algebra.smul_def]
    change b * (Q.generator * (u : B) * (algebraMap A B r)) =
      Q.generator * ((u : B) * (algebraMap A B r * b))
    ring
  rw [he]
  exact (e₁.trans e₂).bijective

/-- 完全oriented prism間の標準イデアル基底変換写像は全単射。 -/
theorem idealTensorMap_bijective (f : Hom P Q) (hf : f.toRingHom = algebraMap A B)
    (hP : P.deltaStructure.IsPerfect) (hQ : Q.deltaStructure.IsPerfect) :
    Function.Bijective (f.idealTensorMap hf) := by
  obtain ⟨u, hu, _⟩ := f.existsUnique_generator_unit hP hQ
  exact f.idealTensorMap_bijective_of_generator_unit hf u hu

/-- p正則なoriented prism間でも標準イデアル基底変換写像は全単射。
源・終域のFrobeniusの全単射性は要求しない。 -/
theorem idealTensorMap_bijective_of_p_regular (f : Hom P Q)
    (hf : f.toRingHom = algebraMap A B)
    (hP : Function.Injective (fun x : A ↦ (p : A) * x))
    (hQ : Function.Injective (fun x : B ↦ (p : B) * x)) :
    Function.Bijective (f.idealTensorMap hf) := by
  obtain ⟨u, hu, _⟩ := f.existsUnique_generator_unit_of_p_regular hP hQ
  exact f.idealTensorMap_bijective_of_generator_unit hf u hu

/-- p正則なoriented prism間の標準テンソル写像を台写像とするB線形同型が存在する。 -/
theorem exists_idealTensorEquiv_of_p_regular (f : Hom P Q)
    (hf : f.toRingHom = algebraMap A B)
    (hP : Function.Injective (fun x : A ↦ (p : A) * x))
    (hQ : Function.Injective (fun x : B ↦ (p : B) * x)) :
    ∃ e : B ⊗[A] P.ideal ≃ₗ[B] Q.ideal, e.toLinearMap = f.idealTensorMap hf :=
  ⟨LinearEquiv.ofBijective (f.idealTensorMap hf)
    (f.idealTensorMap_bijective_of_p_regular hf hP hQ), rfl⟩

/-- 標準イデアル基底変換写像そのものを台写像とする具体的なB線形同型。 -/
def idealTensorEquiv (f : Hom P Q) (hf : f.toRingHom = algebraMap A B)
    (hP : P.deltaStructure.IsPerfect) (hQ : Q.deltaStructure.IsPerfect) :
    B ⊗[A] P.ideal ≃ₗ[B] Q.ideal :=
  LinearEquiv.ofBijective (f.idealTensorMap hf) (f.idealTensorMap_bijective hf hP hQ)

/-- イデアル基底変換同型の台線形写像は標準乗法写像。 -/
@[simp] theorem idealTensorEquiv_toLinearMap (f : Hom P Q)
    (hf : f.toRingHom = algebraMap A B)
    (hP : P.deltaStructure.IsPerfect) (hQ : Q.deltaStructure.IsPerfect) :
    (f.idealTensorEquiv hf hP hQ).toLinearMap = f.idealTensorMap hf := rfl

/-- イデアルの基底変換から終域環への自然な乗法写像は単射。
忠実平坦性を仮定せず、prism射の生成元の剛性で得る。 -/
theorem idealTensorMap_subtype_injective (f : Hom P Q)
    (hf : f.toRingHom = algebraMap A B)
    (hP : P.deltaStructure.IsPerfect) (hQ : Q.deltaStructure.IsPerfect) :
    Function.Injective (Q.ideal.subtype.comp (f.idealTensorMap hf)) :=
  Subtype.val_injective.comp (f.idealTensorMap_bijective hf hP hQ).1

/-- 標準乗法写像の像は終域のprismイデアル全体。 -/
theorem idealTensorMap_subtype_range (f : Hom P Q)
    (hf : f.toRingHom = algebraMap A B)
    (hP : P.deltaStructure.IsPerfect) (hQ : Q.deltaStructure.IsPerfect) :
    LinearMap.range (Q.ideal.subtype.comp (f.idealTensorMap hf)) = Q.ideal := by
  rw [LinearMap.range_comp, LinearMap.range_eq_top.mpr (f.idealTensorMap_bijective hf hP hQ).2]
  simp

end Compatible

/-- 任意の具体的な完全prism射に、その射自身のA代数構造を使う基底変換同型。
別のAlgebraインスタンスや適合性の仮定を外から要求しない。 -/
def idealBaseChangeEquiv (f : Hom P Q)
    (hP : P.deltaStructure.IsPerfect) (hQ : Q.deltaStructure.IsPerfect) :
    letI := f.toRingHom.toAlgebra
    B ⊗[A] P.ideal ≃ₗ[B] Q.ideal := by
  letI := f.toRingHom.toAlgebra
  exact f.idealTensorEquiv rfl hP hQ

/-- 射自身のA代数構造による同型も、純テンソルでは標準乗法に一致する。 -/
@[simp] theorem idealBaseChangeEquiv_tmul (f : Hom P Q)
    (hP : P.deltaStructure.IsPerfect) (hQ : Q.deltaStructure.IsPerfect) (b : B) (x : P.ideal) :
    letI := f.toRingHom.toAlgebra
    (f.idealBaseChangeEquiv hP hQ (b ⊗ₜ[A] x) : B) = b * f.toRingHom x := rfl

end Hom
end SerrePositivity.BhattScholze.OrientedPrism

end OrientedPrismIdealTensor

/-! ## oriented prismの商による同型判定（旧 Prism/Basic/OrientedPrismIsoCriterion.lean）

著者公開版Theorem 3.10の最後のd進完備な環の比較に使う。
既存の完備性による全射判定を使い、核の元の反復除算とd進分離性で単射性を証明する。
p正則なprismへの適用も公開する。perfectoid/prism比較射の存在はこの定理の対象外。
-/

@[expose] public noncomputable section OrientedPrismIsoCriterion

namespace SerrePositivity.BhattScholze.OrientedPrism.Hom
variable {p : ℕ} [Fact p.Prime] {A : Type u} {B : Type v} [CommRing A] [CommRing B]
variable {P : OrientedPrism p A} {Q : OrientedPrism p B}

/-- 完全oriented prism射の生成元の像は非零因子。 -/
theorem map_generator_mul_injective (f : Hom P Q)
    (hP : P.deltaStructure.IsPerfect) (hQ : Q.deltaStructure.IsPerfect) :
    Function.Injective (fun x : B ↦ f.toRingHom P.generator * x) :=
  f.map_generator_mul_injective_of_p_regular hP.p_mul_injective hQ.p_mul_injective

/-- 商射が単射なら台環射も単射。
核の元を生成元で繰り返し割り、d進分離性で零と判定する。 -/
theorem injective_of_quotientMap_injective_of_generator_regular (f : Hom P Q)
    (hgen : Function.Injective (fun x : B ↦ f.toRingHom P.generator * x))
    (hf : Function.Injective f.quotientMap) : Function.Injective f.toRingHom := by
  have hfirst (x : A) (hx : f.toRingHom x = 0) : x ∈ P.ideal := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    apply hf
    rw [f.quotientMap_mk, hx, map_zero, map_zero]
  have hpow (n : ℕ) (x : A) (hx : f.toRingHom x = 0) : x ∈ P.ideal ^ n := by
    induction n generalizing x with
    | zero => simp
    | succ n ih =>
      obtain ⟨y, hy⟩ := Ideal.mem_span_singleton.mp (hfirst x hx)
      have hyker : f.toRingHom y = 0 := by
        apply hgen
        change f.toRingHom P.generator * f.toRingHom y = f.toRingHom P.generator * 0
        rw [mul_zero, ← map_mul, ← hy, hx]
      rw [hy, pow_succ']
      exact Ideal.mul_mem_mul (Ideal.subset_span (by simp)) (ih y hyker)
  apply (injective_iff_map_eq_zero f.toRingHom).mpr
  intro x hx
  let : IsAdicComplete P.ideal A := P.isAdicComplete_generator
  apply IsHausdorff.haus' (I := P.ideal) x
  intro n
  apply SModEq.sub_mem.mpr
  simpa only [sub_zero, smul_eq_mul, Ideal.mul_top] using hpow n x hx

/-- 完全prismの商射が単射なら台環射も単射。既存公開入口を保持する。 -/
theorem injective_of_quotientMap_injective (f : Hom P Q)
    (hP : P.deltaStructure.IsPerfect) (hQ : Q.deltaStructure.IsPerfect)
    (hf : Function.Injective f.quotientMap) : Function.Injective f.toRingHom :=
  f.injective_of_quotientMap_injective_of_generator_regular
    (f.map_generator_mul_injective hP hQ) hf

/-- p正則なoriented prismの商射が単射なら、台環射も単射。 -/
theorem injective_of_quotientMap_injective_of_p_regular (f : Hom P Q)
    (hP : Function.Injective (fun x : A ↦ (p : A) * x))
    (hQ : Function.Injective (fun x : B ↦ (p : B) * x))
    (hf : Function.Injective f.quotientMap) : Function.Injective f.toRingHom :=
  f.injective_of_quotientMap_injective_of_generator_regular
    (f.map_generator_mul_injective_of_p_regular hP hQ) hf

/-- 商射が全射なら台環射も全射。
既存の主イデアル進完備性による全射判定にイデアル像の一致を供給する。 -/
theorem surjective_of_quotientMap_surjective_of_map_ideal_eq (f : Hom P Q)
    (heq : P.ideal.map f.toRingHom = Q.ideal)
    (hf : Function.Surjective f.quotientMap) : Function.Surjective f.toRingHom := by
  let : IsAdicComplete P.ideal A := P.isAdicComplete_generator
  let : IsAdicComplete Q.ideal B := Q.isAdicComplete_generator
  let : IsHausdorff (P.ideal.map f.toRingHom) B := by
    rw [heq]
    infer_instance
  apply surjective_of_mk_map_comp_surjective (I := P.ideal) f.toRingHom
  rw [heq, ← f.quotientMap_comp_mk]
  exact hf.comp Ideal.Quotient.mk_surjective

/-- 完全prismの商射が全射なら台環射も全射。既存公開入口を保持する。 -/
theorem surjective_of_quotientMap_surjective (f : Hom P Q)
    (hP : P.deltaStructure.IsPerfect) (hQ : Q.deltaStructure.IsPerfect)
    (hf : Function.Surjective f.quotientMap) : Function.Surjective f.toRingHom :=
  f.surjective_of_quotientMap_surjective_of_map_ideal_eq (f.map_ideal_eq_of_perfect hP hQ) hf

/-- p正則なoriented prismの商射が全射なら、台環射も全射。 -/
theorem surjective_of_quotientMap_surjective_of_p_regular (f : Hom P Q)
    (hP : Function.Injective (fun x : A ↦ (p : A) * x))
    (hQ : Function.Injective (fun x : B ↦ (p : B) * x))
    (hf : Function.Surjective f.quotientMap) : Function.Surjective f.toRingHom :=
  f.surjective_of_quotientMap_surjective_of_map_ideal_eq (f.map_ideal_eq_of_p_regular hP hQ) hf

/-- p正則なoriented prism射は、標準商射が全単射であることと同値に全単射。
完全性を仮定せず、p正則性と実導来完備性の共通比較を使う。 -/
theorem bijective_iff_quotientMap_bijective_of_p_regular (f : Hom P Q)
    (hP : Function.Injective (fun x : A ↦ (p : A) * x))
    (hQ : Function.Injective (fun x : B ↦ (p : B) * x)) :
    Function.Bijective f.toRingHom ↔ Function.Bijective f.quotientMap := by
  constructor
  · intro hf
    exact (Ideal.quotientEquiv P.ideal Q.ideal (RingEquiv.ofBijective f.toRingHom hf)
      (f.map_ideal_eq_of_p_regular hP hQ).symm).bijective
  · intro hf
    exact ⟨f.injective_of_quotientMap_injective_of_p_regular hP hQ hf.1,
      f.surjective_of_quotientMap_surjective_of_p_regular hP hQ hf.2⟩

/-- 完全oriented prism射は、標準商射が全単射であることと同値に全単射。 -/
theorem bijective_iff_quotientMap_bijective (f : Hom P Q)
    (hP : P.deltaStructure.IsPerfect) (hQ : Q.deltaStructure.IsPerfect) :
    Function.Bijective f.toRingHom ↔ Function.Bijective f.quotientMap := by
  constructor
  · exact f.quotientMap_bijective hP hQ
  · intro h
    exact ⟨f.injective_of_quotientMap_injective hP hQ h.1,
      f.surjective_of_quotientMap_surjective hP hQ h.2⟩

/-- 完全oriented prismの標準商上の全単射から構成する台環の同型。 -/
def ringEquivOfQuotient (f : Hom P Q) (hP : P.deltaStructure.IsPerfect)
    (hQ : Q.deltaStructure.IsPerfect) (hf : Function.Bijective f.quotientMap) : A ≃+* B :=
  RingEquiv.ofBijective f.toRingHom ((f.bijective_iff_quotientMap_bijective hP hQ).mpr hf)

/-- 構成した台環同型は元のprism射を台環射として持つ。 -/
@[simp] theorem ringEquivOfQuotient_toRingHom (f : Hom P Q) (hP : P.deltaStructure.IsPerfect)
    (hQ : Q.deltaStructure.IsPerfect) (hf : Function.Bijective f.quotientMap) :
    (f.ringEquivOfQuotient hP hQ hf).toRingHom = f.toRingHom := rfl

/-- 商上の全単射から構成した台環同型の逆は、再びprism射となる。 -/
def inverseOfQuotient (f : Hom P Q) (hP : P.deltaStructure.IsPerfect)
    (hQ : Q.deltaStructure.IsPerfect) (hf : Function.Bijective f.quotientMap) : Hom Q P := by
  let e := f.ringEquivOfQuotient hP hQ hf
  refine ⟨e.symm.toRingHom, ?_, ?_⟩
  · apply DeltaStructure.IsDeltaHom.symm (e := e)
    exact f.map_delta
  · intro y hy
    rw [← f.map_ideal_eq_of_perfect hP hQ] at hy
    obtain ⟨x, hx, hxy⟩ := Ideal.mem_image_of_mem_map_of_surjective f.toRingHom
      ((f.bijective_iff_quotientMap_bijective hP hQ).mpr hf).2 hy
    change e.symm y ∈ P.ideal
    rw [← hxy]
    change e.symm (e x) ∈ P.ideal
    rw [RingEquiv.symm_apply_apply]
    exact hx

/-- 構成した逆prism射との合成は源の恒等prism射。 -/
@[simp] theorem inverseOfQuotient_comp (f : Hom P Q) (hP : P.deltaStructure.IsPerfect)
    (hQ : Q.deltaStructure.IsPerfect) (hf : Function.Bijective f.quotientMap) :
    (f.inverseOfQuotient hP hQ hf).comp f = Hom.id P := by
  apply Hom.ext
  apply RingHom.ext
  intro x
  change (f.ringEquivOfQuotient hP hQ hf).symm ((f.ringEquivOfQuotient hP hQ hf) x) = x
  exact RingEquiv.symm_apply_apply _ x

/-- 逆prism射との逆順の合成は終域の恒等prism射。 -/
@[simp] theorem comp_inverseOfQuotient (f : Hom P Q) (hP : P.deltaStructure.IsPerfect)
    (hQ : Q.deltaStructure.IsPerfect) (hf : Function.Bijective f.quotientMap) :
    f.comp (f.inverseOfQuotient hP hQ hf) = Hom.id Q := by
  apply Hom.ext
  apply RingHom.ext
  intro x
  change (f.ringEquivOfQuotient hP hQ hf) ((f.ringEquivOfQuotient hP hQ hf).symm x) = x
  exact RingEquiv.apply_symm_apply _ x

end SerrePositivity.BhattScholze.OrientedPrism.Hom

end OrientedPrismIsoCriterion

/-! ## André E1・E2：有界試験 prism への基底射の生成元の単元係数（旧 Andre/Remark715/BoundedPrismHomRigidity.lean）

## 概要

源の生成元が distinguished なら、有界試験 prism への prism 射は生成元を
一意な単元倍へ送る。BS Rem 7.15（著者版 p.62）の一般の基底射への対応。

## 方針

生成元の像の distinguished 性と (p,d) 完備性による Jacobson 条件から係数の単元性を得る。
原典とは異なる有界ねじれからの共通古典的完備性を使う証明。

## 規約

標的の完全性・p 正則性は不要。源には指定生成元の distinguished 性を明示する。

## 使われ方

実完備化の普遍射から、生成元の像が厳密に一致するという補助条件を除く。
-/

@[expose] public noncomputable section BoundedPrismHomRigidity

namespace SerrePositivity.BhattScholze.Andre
open SerrePositivity.DerivedCompletion
variable {p : ℕ} [Fact p.Prime] {A : Type u} {B : Type v} [CommRing A] [CommRing B]
variable {P : OrientedPrism p A} {Q : OrientedPrism p B}
variable (F : OrientedPrism.Hom P Q)
variable (hP : P.deltaStructure.IsDistinguished P.generator)
variable (hB : ∃ N : ℕ, ∀ n : ℕ, ∀ x : B ⧸ Q.ideal,
  (p : B ⧸ Q.ideal) ^ n * x = 0 → (p : B ⧸ Q.ideal) ^ N * x = 0)

include hP hB in
/-- 概要：有界試験 prism への射の生成元の像には一意な単元係数がある。
方針：生成元の像を d*r と書き、distinguished 積の係数の単元性を使う。
規約：標的の p 正則性や完全性を前提に残さない。
使われ方：BS Rem 7.15（著者版 p.62）の一般の基底 prism 射の扱い。 -/
theorem existsUnique_boundedPrismHom_generator_unit :
    ∃! z : Bˣ, F.toRingHom P.generator = Q.generator * z := by
  obtain ⟨r, hr⟩ := Ideal.mem_span_singleton.mp F.map_generator_mem
  have hdist := F.map_delta.map_isDistinguished hP
  rw [hr] at hdist
  let := boundedPrism_pair_isAdicComplete Q hB
  have hru : IsUnit r :=
    (Q.deltaStructure.isDistinguished_factor Q.generator r hdist
      (IsAdicComplete.le_jacobson_bot (Ideal.span {(p : B), Q.generator})
        (Ideal.subset_span (by simp)))
      (IsAdicComplete.le_jacobson_bot (Ideal.span {(p : B), Q.generator})
        (Ideal.subset_span (by simp)))).2
  obtain ⟨z, hz⟩ := hru
  refine ⟨z, by simpa only [hz] using hr, ?_⟩
  intro w hw
  apply Units.ext
  apply Q.generator_regular
  change Q.generator * (w : B) = Q.generator * (z : B)
  exact hw.symm.trans (by simpa only [hz] using hr)

include hP hB in
/-- 概要：基底生成元の像が生成する主イデアルは標的の prism イデアル全体。
方針：生成元の単元係数と主イデアルの単元倍不変性を使う。
規約：選択した orientation 自体の一致は要求しない。
使われ方：BS Rem 7.15（著者版 p.62）の分子の可除性と完備性の移送。 -/
theorem boundedPrismHom_generator_span :
    Ideal.span {F.toRingHom P.generator} = Q.ideal := by
  obtain ⟨z, hz, _⟩ := existsUnique_boundedPrismHom_generator_unit F hP hB
  rw [hz]
  exact Ideal.span_singleton_mul_right_unit z.isUnit Q.generator

include hP hB in
/-- 概要：有界試験 prism への基底生成元の像は非零因子。
方針：標的生成元と一意な単元係数の二つの乗法写像を消去する。
規約：標的の p 正則性は不要。
使われ方：BS Rem 7.15（著者版 p.62）の raw 除算包の試験環への一意普遍射。 -/
theorem boundedPrismHom_generator_regular :
    Function.Injective (fun x : B => F.toRingHom P.generator * x) := by
  obtain ⟨z, hz, _⟩ := existsUnique_boundedPrismHom_generator_unit F hP hB
  intro x y hxy
  change F.toRingHom P.generator * x = F.toRingHom P.generator * y at hxy
  rw [hz, mul_assoc, mul_assoc] at hxy
  exact (IsUnit.isUnit_iff_mulLeft_bijective.mp z.isUnit).1 (Q.generator_regular hxy)

include hP hB in
/-- 概要：有界試験 prism は基底生成元の像に沿って導来完備。
方針：主イデアルの一致で標的の古典的生成元完備性を移し、導来完備性へ戻す。
規約：生成元を取り直した試験 prism を新設しない。
使われ方：BS Rem 7.15（著者版 p.62）の元の実完備化からの比較射。 -/
theorem boundedPrismHom_generator_complete :
    IsModuleComplete B (F.toRingHom P.generator) (ModuleCat.of B B) := by
  let : IsAdicComplete (Ideal.span {F.toRingHom P.generator}) B := by
    rw [boundedPrismHom_generator_span F hP hB]
    exact Q.isAdicComplete_generator
  exact isModuleComplete_of_isAdicComplete B (F.toRingHom P.generator) (ModuleCat.of B B)

include hP hB in
/-- 概要：有界試験 prism への射は prism イデアルを標的のイデアル全体へ写す。
方針：主イデアルの像を生成元の像で計算する。
規約：一般のイデアル保存 prism 射を使う。
使われ方：BS Rem 7.15（著者版 p.62）の基底 prism 上の普遍性。 -/
theorem boundedPrismHom_map_ideal_eq : P.ideal.map F.toRingHom = Q.ideal := by
  rw [OrientedPrism.ideal, Ideal.map_span, Set.image_singleton]
  exact boundedPrismHom_generator_span F hP hB

end SerrePositivity.BhattScholze.Andre

end BoundedPrismHomRigidity
