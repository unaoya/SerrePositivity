module

public import SerrePositivity.CommutativeAlgebra.Almost.Category
public import SerrePositivity.CommutativeAlgebra.PowerTorsion.Basic
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.Module
public import Mathlib.Algebra.Module.Torsion.Basic

/-!
# 商環上の almost 条件と係数制限

商の核で零化される加群に実際の商環作用を与える。商写像の全射性から、
イデアルの像に関する almost 零性と、元の環での almost 零性を比較する。
線形写像の核・余核の almost 条件も係数制限と一致する。
商環でのイデアルの冪等性は、almost 圏への適用時に明示して受け取る。
-/

@[expose] public noncomputable section

universe u v w z

namespace SerrePositivity.Almost

open CategoryTheory CategoryTheory.Limits

variable {R : Type u} [CommRing R]

section SurjectiveAlgebra

variable {S : Type v} [CommRing S] [Algebra R S]
variable {M : Type w} [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]

/-- 全射な代数写像に沿うイデアルの像による almost 零性は、係数制限前の条件と一致。
像のイデアルの各元を基底環へ持ち上げ、両環のスカラー作用の両立を使う。 -/
theorem isAlmostZero_map_iff_of_surjective (I : Ideal R)
    (hs : Function.Surjective (algebraMap R S)) :
    IsAlmostZero (I.map (algebraMap R S)) M ↔ IsAlmostZero I M := by
  rw [IsAlmostZero.iff_smul_eq_zero, IsAlmostZero.iff_smul_eq_zero]
  constructor
  · intro h a ha m
    simpa only [IsScalarTower.algebraMap_smul] using
      h (algebraMap R S a) (Ideal.mem_map_of_mem _ ha) m
  · intro h b hb m
    obtain ⟨a, ha, rfl⟩ := (Ideal.mem_map_iff_of_surjective _ hs).mp hb
    simpa only [IsScalarTower.algebraMap_smul] using h a ha m

variable {N : Type z} [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N]

/-- 全射な係数変更に沿ってイデアルを写すと、線形写像の almost 単射条件は係数制限と一致。
核の元を零化する条件を使うので、核の別々の加群構造を同一視する必要はない。 -/
theorem isAlmostInjective_map_iff_restrictScalars (I : Ideal R)
    (hs : Function.Surjective (algebraMap R S)) (f : M →ₗ[S] N) :
    IsAlmostInjective (I.map (algebraMap R S)) f ↔
      IsAlmostInjective I (f.restrictScalars R) := by
  rw [IsAlmostInjective.iff_smul_eq_zero, IsAlmostInjective.iff_smul_eq_zero]
  constructor
  · intro h x hx a ha
    simpa only [IsScalarTower.algebraMap_smul] using
      h x hx (algebraMap R S a) (Ideal.mem_map_of_mem _ ha)
  · intro h x hx b hb
    obtain ⟨a, ha, rfl⟩ := (Ideal.mem_map_iff_of_surjective _ hs).mp hb
    simpa only [IsScalarTower.algebraMap_smul] using h x hx a ha

/-- 全射な係数変更に沿ってイデアルを写すと、線形写像の almost 全射条件は係数制限と一致。
像に属する条件を元の持ち上げで比較する。 -/
theorem isAlmostSurjective_map_iff_restrictScalars (I : Ideal R)
    (hs : Function.Surjective (algebraMap R S)) (f : M →ₗ[S] N) :
    IsAlmostSurjective (I.map (algebraMap R S)) f ↔
      IsAlmostSurjective I (f.restrictScalars R) := by
  rw [IsAlmostSurjective.iff_smul_mem_range, IsAlmostSurjective.iff_smul_mem_range]
  constructor
  · intro h a ha y
    simpa only [IsScalarTower.algebraMap_smul, LinearMap.mem_range,
      LinearMap.restrictScalars_apply] using
      h (algebraMap R S a) (Ideal.mem_map_of_mem _ ha) y
  · intro h b hb y
    obtain ⟨a, ha, rfl⟩ := (Ideal.mem_map_iff_of_surjective _ hs).mp hb
    simpa only [IsScalarTower.algebraMap_smul, LinearMap.mem_range,
      LinearMap.restrictScalars_apply] using h a ha y

/-- 全射な係数変更の下で、線形写像の核・余核による almost 同型条件は係数制限と一致。 -/
theorem isAlmostIso_map_iff_restrictScalars (I : Ideal R)
    (hs : Function.Surjective (algebraMap R S)) (f : M →ₗ[S] N) :
    IsAlmostIso (I.map (algebraMap R S)) f ↔ IsAlmostIso I (f.restrictScalars R) :=
  and_congr (isAlmostInjective_map_iff_restrictScalars I hs f)
    (isAlmostSurjective_map_iff_restrictScalars I hs f)

end SurjectiveAlgebra

section PowTorsion

variable {S : Type u} [CommRing S] [Algebra R S]
variable {M : Type u} [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]

/-- 全射な代数写像に沿ってイデアルを写すと、加群の冪ねじれ条件は係数制限前後で一致。
各冪での almost 零性を比較し、イデアルの像が冪を保つことを用いる。
両側で同じ零化指数を使えるので、正規化長さの定義域の比較に適用できる。 -/
theorem isPowTorsion_map_iff_of_surjective (J : Ideal R)
    (hs : Function.Surjective (algebraMap R S)) :
    IsPowTorsion (J.map (algebraMap R S)) M ↔ IsPowTorsion J M := by
  apply exists_congr
  intro n
  simpa only [Module.isTorsionBySet_iff_subset_annihilator, SetLike.coe_subset_coe,
    IsAlmostZero, Ideal.map_pow] using
    isAlmostZero_map_iff_of_surjective (J ^ n) hs (M := M)

end PowTorsion

section QuotientAction

variable (K : Ideal R) (M : Type v) [AddCommGroup M] [Module R M]

/-- 核イデアル `K` が加群を零化するときの、具体的な `R/K` 加群構造。
Mathlib のねじれ加群の商環作用を用い、商元の代表の選択に依存しない作用を構成する。 -/
@[instance_reducible]
def quotientModule (hK : IsAlmostZero K M) : Module (R ⧸ K) M :=
  ((Module.isTorsionBySet_iff_subset_annihilator R M).mpr hK).module

/-- 構成した商環作用は、商写像を通じた元の環の作用と一致する。 -/
theorem quotientModule_mk_smul (hK : IsAlmostZero K M) (a : R) (m : M) :
    let _ := quotientModule K M hK
    Ideal.Quotient.mk K a • m = a • m := rfl

/-- 構成した商環作用と元の環の作用はスカラー塔をなす。
商の代表元で確認することで、標準的な商環の代数構造との両立を得る。 -/
theorem quotientModule_scalarTower (hK : IsAlmostZero K M) :
    let _ := quotientModule K M hK
    IsScalarTower R (R ⧸ K) M := by
  let := quotientModule K M hK
  apply IsScalarTower.of_algebraMap_smul
  intro a m
  exact quotientModule_mk_smul K M hK a m

/-- `K` で零化される加群について、商環での像イデアルによる almost 零性は元の条件と一致。
明示的に構成した商環作用を用いて、全射代数写像の一般補題を適用する。 -/
theorem isAlmostZero_quotient_iff (I : Ideal R) (hK : IsAlmostZero K M) :
    let _ := quotientModule K M hK
    IsAlmostZero (I.map (Ideal.Quotient.mk K)) M ↔ IsAlmostZero I M := by
  let := quotientModule K M hK
  let := quotientModule_scalarTower K M hK
  exact isAlmostZero_map_iff_of_surjective I (Ideal.Quotient.mk_surjective)

end QuotientAction

section QuotientMaps

variable (K : Ideal R)
variable {M : Type v} [AddCommGroup M] [Module R M]
variable {N : Type w} [AddCommGroup N] [Module R N]

/-- 核イデアルで零化される二つの加群の線形写像を、実際の商環上の線形写像にする。
商元を基底環へ持ち上げて、元の線形性から商環上の線形性を確認する。 -/
def quotientLinearMap (hM : IsAlmostZero K M) (hN : IsAlmostZero K N)
    (f : M →ₗ[R] N) :
    let _ := quotientModule K M hM
    let _ := quotientModule K N hN
    M →ₗ[R ⧸ K] N := by
  let := quotientModule K M hM
  let := quotientModule K N hN
  exact {
    toFun := f
    map_add' := f.map_add
    map_smul' := fun a m => by
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
      exact f.map_smul a m }

/-- 構成した商環上の線形写像の係数を元の環へ制限すると、元の線形写像に戻る。
写像の値は構成時から変更していないので、外延性で一致する。 -/
theorem quotientLinearMap_restrictScalars (hM : IsAlmostZero K M) (hN : IsAlmostZero K N)
    (f : M →ₗ[R] N) :
    let _ := quotientModule K M hM
    let _ := quotientModule K N hN
    let _ := quotientModule_scalarTower K M hM
    let _ := quotientModule_scalarTower K N hN
    (quotientLinearMap K hM hN f).restrictScalars R = f := by
  let := quotientModule K M hM
  let := quotientModule K N hN
  let := quotientModule_scalarTower K M hM
  let := quotientModule_scalarTower K N hN
  ext m
  rfl

/-- 核で零化される加群間の写像について、商環の像イデアルによる almost 単射条件は元の条件と一致。 -/
theorem isAlmostInjective_quotientLinearMap_iff (I : Ideal R)
    (hM : IsAlmostZero K M) (hN : IsAlmostZero K N) (f : M →ₗ[R] N) :
    let _ := quotientModule K M hM
    let _ := quotientModule K N hN
    IsAlmostInjective (I.map (Ideal.Quotient.mk K)) (quotientLinearMap K hM hN f) ↔
      IsAlmostInjective I f := by
  let := quotientModule K M hM
  let := quotientModule K N hN
  let := quotientModule_scalarTower K M hM
  let := quotientModule_scalarTower K N hN
  simpa only [quotientLinearMap_restrictScalars, Ideal.Quotient.algebraMap_eq] using
    isAlmostInjective_map_iff_restrictScalars I (Ideal.Quotient.mk_surjective)
      (quotientLinearMap K hM hN f)

/-- 核で零化される加群間の写像について、商環の像イデアルによる almost 全射条件は元の条件と一致。 -/
theorem isAlmostSurjective_quotientLinearMap_iff (I : Ideal R)
    (hM : IsAlmostZero K M) (hN : IsAlmostZero K N) (f : M →ₗ[R] N) :
    let _ := quotientModule K M hM
    let _ := quotientModule K N hN
    IsAlmostSurjective (I.map (Ideal.Quotient.mk K)) (quotientLinearMap K hM hN f) ↔
      IsAlmostSurjective I f := by
  let := quotientModule K M hM
  let := quotientModule K N hN
  let := quotientModule_scalarTower K M hM
  let := quotientModule_scalarTower K N hN
  simpa only [quotientLinearMap_restrictScalars, Ideal.Quotient.algebraMap_eq] using
    isAlmostSurjective_map_iff_restrictScalars I (Ideal.Quotient.mk_surjective)
      (quotientLinearMap K hM hN f)

/-- 核で零化される加群間の写像について、商環の像イデアルによる almost 同型条件は元の条件と一致。 -/
theorem isAlmostIso_quotientLinearMap_iff (I : Ideal R)
    (hM : IsAlmostZero K M) (hN : IsAlmostZero K N) (f : M →ₗ[R] N) :
    let _ := quotientModule K M hM
    let _ := quotientModule K N hN
    IsAlmostIso (I.map (Ideal.Quotient.mk K)) (quotientLinearMap K hM hN f) ↔
      IsAlmostIso I f := by
  let := quotientModule K M hM
  let := quotientModule K N hN
  exact and_congr (isAlmostInjective_quotientLinearMap_iff K I hM hN f)
    (isAlmostSurjective_quotientLinearMap_iff K I hM hN f)

end QuotientMaps

section QuotientCategory

variable (K I : Ideal R)
variable [Fact ((I.map (Ideal.Quotient.mk K)) * (I.map (Ideal.Quotient.mk K)) =
  I.map (Ideal.Quotient.mk K))]

/-- 商環で像イデアルの冪等性が与えられているとき、almost 圏での零性は元の環の almost 零性と一致。
元のイデアルの冪等性は要求せず、商環側の冪等性は独立した仮定として明示する。 -/
theorem isZero_quotient_localization_obj_iff (M : ModuleCat.{u} R)
    (hK : IsAlmostZero K M) :
    let _ := quotientModule K M hK
    IsZero ((localization (I.map (Ideal.Quotient.mk K))).obj (ModuleCat.of (R ⧸ K) M)) ↔
      IsAlmostZero I M := by
  let := quotientModule K M hK
  exact (isZero_localization_obj_iff (I.map (Ideal.Quotient.mk K))
    (ModuleCat.of (R ⧸ K) M)).trans (isAlmostZero_quotient_iff K M I hK)

/-- 商環で像イデアルの冪等性が与えられているとき、商環の almost 圏で写像が同型になる条件は
元の環での核・余核の almost 零性と一致する。実際の almost 局所化圏の同型判定を使う。 -/
theorem isIso_quotient_localization_map_iff {M N : ModuleCat.{u} R}
    (hM : IsAlmostZero K M) (hN : IsAlmostZero K N) (f : M ⟶ N) :
    let _ := quotientModule K M hM
    let _ := quotientModule K N hN
    IsIso ((localization (I.map (Ideal.Quotient.mk K))).map
      (ModuleCat.ofHom (quotientLinearMap K hM hN f.hom))) ↔ IsAlmostIso I f.hom := by
  let := quotientModule K M hM
  let := quotientModule K N hN
  exact (isIso_localization_map_iff_isAlmostIso (I.map (Ideal.Quotient.mk K))
    (ModuleCat.ofHom (quotientLinearMap K hM hN f.hom))).trans
    (isAlmostIso_quotientLinearMap_iff K I hM hN f.hom)

end QuotientCategory

/-- `f` の冪で生成される主イデアルが加群を零化することと、その冪の各元への作用が零であることは同値。
`p^N` による零化の仮定を、具体的な商環作用の構成へ渡すための補題。 -/
theorem isAlmostZero_span_pow_iff (f : R) (N : ℕ) (M : Type v)
    [AddCommGroup M] [Module R M] :
    IsAlmostZero (Ideal.span {f ^ N}) M ↔ ∀ m : M, (f ^ N) • m = 0 := by
  simp only [IsAlmostZero, Ideal.span_le, Set.singleton_subset_iff,
    SetLike.mem_coe, Module.mem_annihilator]

/-- 商の核が `f` の冪を含み、加群を零化すれば、その加群は導来 `f` 完備。
商環作用の構成に必要な零化条件を、既存の実導来圏での完備性の証明へ接続する。 -/
theorem isModuleComplete_of_quotient_annihilator (K : Ideal R) (f : R) (N : ℕ)
    (M : ModuleCat.{u} R) (hK : IsAlmostZero K M) (hN : f ^ N ∈ K) :
    DerivedCompletion.IsModuleComplete R f M :=
  DerivedCompletion.isModuleComplete_of_pow_smul_zero R f M N
    (fun m => hK.smul_eq_zero hN m)

end SerrePositivity.Almost
