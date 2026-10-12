module

public import SerrePositivity.Paper.Section2.PerfectApproximation
public import SerrePositivity.CommutativeAlgebra.PresentationBaseChange
public import SerrePositivity.CommutativeAlgebra.SeparableBaseChange
public import SerrePositivity.CommutativeAlgebra.LocalAlgebra
public import SerrePositivity.CommutativeAlgebra.RegularLocalRing

/-!
# 塔の有限段から perfection の近似への係数拡大

各段 `A_n` の作用を `D^{1/pⁿ}` に構成し、
`Λ ⊗_{A_n} D^{1/pⁿ} → D_perf` の自然な写像を扱う。
写像の像は既に定義した近似部分代数である。
塔の分数体の純非分離性と、根の段の分数体の分離性を示し、
平坦性と局所化からテンソル積全体の単射性を導く。
剰余体が同じ完全体である論文の設定では、近似部分代数との同型が得られる。
正則な各段の被約性は、証明済みの正則パラメータの定理から従う。
-/

public section
universe u
namespace SerrePositivity.Section2
open scoped TensorProduct
open MvPolynomial

variable (A D : Type u) [CommRing A] [CommRing D] [Algebra A D]
    (p : ℕ) [Fact p.Prime] [CharP D p] [IsReduced D]
    {h : ℕ} (t : Fin h → A)

omit [Algebra A D] [IsReduced D] in
/-- 正則パラメータから作った塔は、単射な基底写像に沿って perfection に埋め込まれる。
各段の正則性から被約性を得る部分は、証明済みの正則パラメータの定理から従う。
新しい未証明の仮定は導入しない。 -/
theorem towerToPerfection_injective_of_regular [IsRegularLocalRing A]
    [Algebra A (PerfectClosure D p)]
    (ht : Ideal.span (Set.range t) = IsLocalRing.maximalIdeal A)
    (hdim : ringKrullDim A = h)
    (hinj : Function.Injective (algebraMap A (PerfectClosure D p))) :
    Function.Injective (towerToPerfect A (PerfectClosure D p) t p) := by
  have hregular := isRegularLocalRing_towerStage A t p ht hdim
  have hcharA : CharP A p := (algebraMap A (PerfectClosure D p)).charP hinj p
  apply towerToPerfect_injective A (PerfectClosure D p) t p
  · intro n
    let := hregular n
    let := towerStage_free A t p n
    exact charP_of_injective_algebraMap (FaithfulSMul.algebraMap_injective A _) p
  · intro n
    let := hregular n
    let := isDomain_of_isRegularLocalRing (TowerStage A t p n)
    infer_instance
  · exact hinj

omit [Algebra A D] [CharP D p] [IsReduced D] in
/-- 塔の分数体は、各有限段の分数体上純非分離である。
実際には底体 `K` が有限段を含めば十分で、`K` の局所化の性質は使わない。
塔の元に対する Frobenius の公式を、分子と分母に適用する。 -/
theorem tower_fractionRing_isPurelyInseparable (n : ℕ)
    (K E : Type u) [Field K] [Field E] [ExpChar K p]
    [Algebra (TowerStage A t p n) K] [Algebra K E]
    [Algebra (Tower A t p) E] [IsFractionRing (Tower A t p) E]
    [Algebra (TowerStage A t p n) E]
    [IsScalarTower (TowerStage A t p n) K E]
    [IsScalarTower (TowerStage A t p n) (Tower A t p) E]
    (hchar : ∀ m, CharP (TowerStage A t p m) p) :
    IsPurelyInseparable K E := by
  apply isPurelyInseparable_fractionRing_of_pow_mem (Tower A t p) K E p
  intro x
  obtain ⟨m, a, ha⟩ := tower_pow_mem_range A t p hchar x
  refine ⟨m, algebraMap (TowerStage A t p n) K
    (algebraMap A (TowerStage A t p n) a), ?_⟩
  rw [← IsScalarTower.algebraMap_apply (TowerStage A t p n) K E,
    IsScalarTower.algebraMap_apply (TowerStage A t p n) (Tower A t p) E,
    ← IsScalarTower.algebraMap_apply A (TowerStage A t p n) (Tower A t p), ha, map_pow]

/-- `A_n` から `D^{1/pⁿ}` への写像。係数は通常の包含、変数はパラメータの根に送る。 -/
noncomputable def towerStageToRootStage (n : ℕ) :
    TowerStage A t p n →+* perfectionRootStage D p n := by
  let f : A →+* perfectionRootStage D p n :=
    (perfectionRootStageBaseMap D p n).comp (algebraMap A D)
  let z : Fin h → perfectionRootStage D p n :=
    fun i ↦ perfectionRootStageEquiv D p n (algebraMap A D (t i))
  apply Ideal.Quotient.lift _ (eval₂Hom f z)
  change towerRel A t p n ≤ RingHom.ker (eval₂Hom f z)
  rw [towerRel, relIdeal, Ideal.span_le]
  rintro _ ⟨i, rfl⟩
  change eval₂Hom f z (X i ^ (p ^ n) - C (t i)) = 0
  rw [map_sub, map_pow, eval₂Hom_X', eval₂Hom_C, sub_eq_zero]
  apply Subtype.ext
  simp only [z, f, RingHom.comp_apply, Subring.coe_pow, perfectionRootStageEquiv_coe]
  rw [perfectionRootHom_apply, perfection_mk_pow, perfectionRootStageBaseMap_coe]

/-- 有限段の係数は、根の段への通常の包含に送られる。 -/
theorem towerStageToRootStage_algebraMap (n : ℕ) (a : A) :
    towerStageToRootStage A D p t n (algebraMap A (TowerStage A t p n) a) =
      perfectionRootStageBaseMap D p n (algebraMap A D a) := by
  change eval₂Hom ((perfectionRootStageBaseMap D p n).comp (algebraMap A D))
    (fun i ↦ perfectionRootStageEquiv D p n (algebraMap A D (t i))) (C a) = _
  rw [eval₂Hom_C]
  rfl

/-- 有限段の変数の像は、対応するパラメータの根である。 -/
theorem towerStageToRootStage_mk_X (n : ℕ) (i : Fin h) :
    towerStageToRootStage A D p t n (Ideal.Quotient.mk (towerRel A t p n) (X i)) =
      perfectionRootStageEquiv D p n (algebraMap A D (t i)) := by
  change eval₂Hom ((perfectionRootStageBaseMap D p n).comp (algebraMap A D))
    (fun i ↦ perfectionRootStageEquiv D p n (algebraMap A D (t i))) (X i) = _
  rw [eval₂Hom_X']

/-- 有限段と根の段の Frobenius 同型は、基底環からの包含と両立する。
したがって根の段の分離性を、元の `A → D` の生成的分離性に戻せる。 -/
theorem towerStageToRootStage_frobenius [CharP A p] (n : ℕ) (x : TowerStage A t p n) :
    perfectionRootStageEquiv D p n (algebraMap A D (towerStageFrobenius A t p n x)) =
      towerStageToRootStage A D p t n x := by
  have heq : (perfectionRootStageEquiv D p n).toRingHom.comp
      ((algebraMap A D).comp (towerStageFrobenius A t p n)) =
      towerStageToRootStage A D p t n := by
    apply Ideal.Quotient.ringHom_ext
    apply MvPolynomial.ringHom_ext
    · intro a
      change perfectionRootStageEquiv D p n (algebraMap A D
        (towerStageFrobenius A t p n (algebraMap A (TowerStage A t p n) a))) =
        towerStageToRootStage A D p t n (algebraMap A (TowerStage A t p n) a)
      rw [towerStageFrobenius_algebraMap, map_pow, perfectionRootStageEquiv_pow,
        towerStageToRootStage_algebraMap]
    · intro i
      change perfectionRootStageEquiv D p n (algebraMap A D
        (towerStageFrobenius A t p n (stageX A t p n i))) =
        towerStageToRootStage A D p t n (stageX A t p n i)
      rw [towerStageFrobenius_stageX, towerStageToRootStage_mk_X]
  exact RingHom.congr_fun heq x

/-- 根の段への写像を perfection に入れると、既存の完全環への写像と一致する。 -/
theorem towerStageToRootStage_coe [Algebra A (PerfectClosure D p)]
    (hbase : ∀ a : A, algebraMap A (PerfectClosure D p) a =
      PerfectClosure.of D p (algebraMap A D a)) (n : ℕ) (x : TowerStage A t p n) :
    (towerStageToRootStage A D p t n x : PerfectClosure D p) =
      towerStageToPerfect A (PerfectClosure D p) t p n x := by
  have heq : (perfectionRootStage D p n).subtype.comp (towerStageToRootStage A D p t n) =
      (towerStageToPerfect A (PerfectClosure D p) t p n).toRingHom := by
    apply Ideal.Quotient.ringHom_ext
    apply MvPolynomial.ringHom_ext
    · intro a
      change (towerStageToRootStage A D p t n
        (algebraMap A (TowerStage A t p n) a) : PerfectClosure D p) =
        towerStageToPerfect A (PerfectClosure D p) t p n
          (algebraMap A (TowerStage A t p n) a)
      rw [towerStageToRootStage_algebraMap, perfectionRootStageBaseMap_coe,
        AlgHom.commutes, hbase]
    · intro i
      change (towerStageToRootStage A D p t n
        (Ideal.Quotient.mk _ (X i)) : PerfectClosure D p) =
        towerStageToPerfect A (PerfectClosure D p) t p n (Ideal.Quotient.mk _ (X i))
      rw [towerStageToRootStage_mk_X, towerStageToPerfect_mk_X]
      rw [perfectionRootStageEquiv_coe]
      apply (iterateFrobeniusEquiv (PerfectClosure D p) p n).injective
      rw [iterateFrobeniusEquiv_def, iterateFrobeniusEquiv_def,
        perfectionRootHom_apply, perfection_mk_pow, perfectRoot_pow, hbase]
  exact RingHom.congr_fun heq x

end SerrePositivity.Section2


namespace SerrePositivity.Section2
open scoped TensorProduct

variable (A D : Type u) [CommRing A] [CommRing D] [Algebra A D]
    (p : ℕ) [Fact p.Prime] [CharP D p] [IsReduced D]
    {h : ℕ} (t : Fin h → A) [Algebra A (PerfectClosure D p)]

/-- 根の段に対する `A_n` の作用。インスタンスの登録はこのファイル内に限る。 -/
noncomputable local instance rootStageAlgebra (n : ℕ) :
    Algebra (TowerStage A t p n) (perfectionRootStage D p n) :=
  (towerStageToRootStage A D p t n).toAlgebra

omit [Algebra A (PerfectClosure D p)] in
/-- 根の段の分数体は、有限段の分数体上分離的。
両方の根の段を Frobenius 同型で元の環に戻し、生成的分離性を移す。
各有限段の被約性も、証明済みの正則パラメータの定理から従う。 -/
theorem rootStage_fractionRing_isSeparable [IsRegularLocalRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A] [CharP A p]
    [CharP (IsLocalRing.ResidueField A) p] [PerfectRing (IsLocalRing.ResidueField A) p]
    (ht : Ideal.span (Set.range t) = IsLocalRing.maximalIdeal A)
    (hdim : ringKrullDim A = h)
    (hsep : ∀ d : D, ((minpoly A d).map (algebraMap A (FractionRing A))).Separable)
    (n : ℕ) (K L : Type u) [Field K] [Field L]
    [Algebra (TowerStage A t p n) K] [IsFractionRing (TowerStage A t p n) K]
    [Algebra (perfectionRootStage D p n) L] [IsFractionRing (perfectionRootStage D p n) L]
    [Algebra (TowerStage A t p n) L] [Algebra K L]
    [IsScalarTower (TowerStage A t p n) (perfectionRootStage D p n) L]
    [IsScalarTower (TowerStage A t p n) K L] : Algebra.IsSeparable K L := by
  let := isDomain_of_isRegularLocalRing A
  let := isRegularLocalRing_towerStage A t p ht hdim n
  let := isDomain_of_isRegularLocalRing (TowerStage A t p n)
  let := towerStage_free A t p n
  let : CharP (TowerStage A t p n) p :=
    charP_of_injective_algebraMap (FaithfulSMul.algebraMap_injective A _) p
  let eA := towerStageFrobeniusEquiv A t p ht n
  apply isSeparable_fractionRing_of_equiv A D (TowerStage A t p n)
    (perfectionRootStage D p n) K L eA.symm (perfectionRootStageEquiv D p n) _ hsep
  intro a
  have hf : towerStageFrobenius A t p n (eA.symm a) = a := by
    rw [← towerStageFrobeniusEquiv_apply A t p ht n]
    exact eA.apply_symm_apply a
  change perfectionRootStageEquiv D p n (algebraMap A D a) =
    towerStageToRootStage A D p t n (eA.symm a)
  simpa only [hf] using towerStageToRootStage_frobenius A D p t n (eA.symm a)

/-- Perfection に対する塔の標準作用。 -/
noncomputable local instance towerPerfectionAlgebra :
    Algebra (Tower A t p) (PerfectClosure D p) :=
  (towerToPerfect A (PerfectClosure D p) t p).toRingHom.toAlgebra

/-- 塔を経由した有限段の作用。 -/
noncomputable local instance stagePerfectionAlgebra (n : ℕ) :
    Algebra (TowerStage A t p n) (PerfectClosure D p) :=
  ((towerToPerfect A (PerfectClosure D p) t p).toRingHom.comp (towerOf A t p n)).toAlgebra

/-- 有限段と塔の作用は構成から両立する。 -/
local instance stageTowerPerfection (n : ℕ) :
    IsScalarTower (TowerStage A t p n) (Tower A t p) (PerfectClosure D p) :=
  IsScalarTower.of_algebraMap_eq fun _ ↦ rfl

variable (hbase : ∀ a : A, algebraMap A (PerfectClosure D p) a =
    PerfectClosure.of D p (algebraMap A D a))

/-- 根の段の包含は `A_n` の作用を保つ。 -/
noncomputable def rootStageInclusion (n : ℕ) :
    perfectionRootStage D p n →ₐ[TowerStage A t p n] PerfectClosure D p where
  __ := (perfectionRootStage D p n).subtype
  commutes' x := by
    exact (towerStageToRootStage_coe A D p t hbase n x).trans
      (towerToPerfect_of A (PerfectClosure D p) t p n x).symm

/-- 根の段から近似部分代数への自然な包含。商のイデアルを拡大する際に用いる。 -/
noncomputable def rootStageToApproximation (n : ℕ) :
    perfectionRootStage D p n →+* perfectionApproximation D p (Tower A t p) n where
  toFun d := ⟨d, Algebra.subset_adjoin d.property⟩
  map_one' := Subtype.ext rfl
  map_mul' _ _ := Subtype.ext rfl
  map_zero' := Subtype.ext rfl
  map_add' _ _ := Subtype.ext rfl

omit [Algebra A D] [IsReduced D] in
/-- 根の段の包含は、perfection 内の元を変えない。 -/
@[simp] theorem rootStageToApproximation_coe (n : ℕ) (d : perfectionRootStage D p n) :
    (rootStageToApproximation A D p t n d : PerfectClosure D p) = d := by rfl

/-- `Λ ⊗_{A_n} D^{1/pⁿ}` から perfection への自然な `Λ` 代数準同型。 -/
noncomputable def perfectBaseChangeMap (n : ℕ) :
    Tower A t p ⊗[TowerStage A t p n] perfectionRootStage D p n →ₐ[Tower A t p]
      PerfectClosure D p :=
  Algebra.TensorProduct.productLeftAlgHom (Algebra.ofId (Tower A t p) (PerfectClosure D p))
    (rootStageInclusion A D p t hbase n)

omit [Algebra A D] in
/-- 近似環を経由してイデアルを perfection へ拡大しても、標準写像による拡大と同じ。
したがって商写像の行き先は、近似段によらず同じ `C/HC` である。 -/
theorem rootStageToApproximation_map_extension (n : ℕ) (H : Ideal D) :
    ((H.map (perfectionRootStageBaseMap D p n)).map
      (rootStageToApproximation A D p t n)).map
        (algebraMap (perfectionApproximation D p (Tower A t p) n) (PerfectClosure D p)) =
      H.map (PerfectClosure.of D p) := by
  rw [Ideal.map_map, Ideal.map_map]
  congr 1
  apply RingHom.ext
  intro x
  change (rootStageToApproximation A D p t n
    (perfectionRootStageBaseMap D p n x) : PerfectClosure D p) = _
  rw [rootStageToApproximation_coe, perfectionRootStageBaseMap_coe]

/-- 単純テンソルは、塔からの像と根の段の元との積に写る。 -/
@[simp] theorem perfectBaseChangeMap_tmul (n : ℕ) (a : Tower A t p)
    (d : perfectionRootStage D p n) :
    perfectBaseChangeMap A D p t hbase n (a ⊗ₜ[TowerStage A t p n] d) =
      towerToPerfect A (PerfectClosure D p) t p a * (d : PerfectClosure D p) := by
  rfl

section Injectivity
attribute [local instance] FractionRing.liftAlgebra

/-- 生成的分離な有限段と純非分離な塔の係数拡大は、perfection に単射に入る。
各因子を共通の分数体へ入れ、平坦性と分離・純非分離の線形無関連性を適用する。 -/
theorem perfectBaseChangeMap_injective [IsDomain D] [IsRegularLocalRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    [CharP (IsLocalRing.ResidueField A) p] [PerfectRing (IsLocalRing.ResidueField A) p]
    (ht : Ideal.span (Set.range t) = IsLocalRing.maximalIdeal A)
    (hdim : ringKrullDim A = h) (hinj : Function.Injective (algebraMap A D))
    (hsep : ∀ d : D, ((minpoly A d).map (algebraMap A (FractionRing A))).Separable)
    (n : ℕ) : Function.Injective (perfectBaseChangeMap A D p t hbase n) := by
  let C := PerfectClosure D p
  let B := TowerStage A t p n
  let R := Tower A t p
  let T := perfectionRootStage D p n
  let := perfectClosure_isDomain D p
  let := isDomain_of_isRegularLocalRing A
  let : CharP A p := (algebraMap A D).charP hinj p
  let := isRegularLocalRing_towerStage A t p ht hdim n
  let : IsDomain B := isDomain_of_isRegularLocalRing B
  let := towerStage_free A t p n
  have hchar (m : ℕ) : CharP (TowerStage A t p m) p := by
    let := isRegularLocalRing_towerStage A t p ht hdim m
    let := towerStage_free A t p m
    exact charP_of_injective_algebraMap (FaithfulSMul.algebraMap_injective A _) p
  let := hchar n
  have hof : Function.Injective (PerfectClosure.of D p) := fun x y hxy ↦
    (PerfectClosure.eq_iff D p (0, x) (0, y)).mp hxy
  have hAC : Function.Injective (algebraMap A C) := by
    intro a b hab
    apply hinj
    apply hof
    change algebraMap A (PerfectClosure D p) a = algebraMap A (PerfectClosure D p) b at hab
    simpa only [hbase] using hab
  have hRC := towerToPerfection_injective_of_regular A D p t ht hdim hAC
  let : IsDomain R := Function.Injective.isDomain
    (towerToPerfect A C t p).toRingHom hRC
  let : FaithfulSMul R C := (faithfulSMul_iff_algebraMap_injective R C).mpr hRC
  let : Algebra T C := T.subtype.toAlgebra
  let : IsScalarTower B T C := IsScalarTower.of_algebraMap_eq fun x ↦
    ((rootStageInclusion A D p t hbase n).commutes x).symm
  have hBC : Function.Injective (algebraMap B C) := by
    intro x y hxy
    apply towerStageToPerfect_injective A C t p n hAC
    change towerToPerfect A C t p (towerOf A t p n x) =
      towerToPerfect A C t p (towerOf A t p n y) at hxy
    simpa only [towerToPerfect_of] using hxy
  let : FaithfulSMul B C := (faithfulSMul_iff_algebraMap_injective B C).mpr hBC
  let : FaithfulSMul T C := (faithfulSMul_iff_algebraMap_injective T C).mpr Subtype.val_injective
  let : FaithfulSMul B R := (faithfulSMul_iff_algebraMap_injective B R).mpr
    (fun x y hxy ↦ hBC (by
      rw [IsScalarTower.algebraMap_apply B R C, IsScalarTower.algebraMap_apply B R C, hxy]))
  let : FaithfulSMul B T := (faithfulSMul_iff_algebraMap_injective B T).mpr
    (fun x y hxy ↦ hBC (by
      rw [IsScalarTower.algebraMap_apply B T C, IsScalarTower.algebraMap_apply B T C, hxy]))
  let : Module.Flat B R := flat_tower A t p n
  let : CharP (FractionRing B) p :=
    charP_of_injective_algebraMap (IsFractionRing.injective B _) p
  let : IsPurelyInseparable (FractionRing B) (FractionRing R) :=
    tower_fractionRing_isPurelyInseparable A p t n _ _ hchar
  let : Algebra.IsSeparable (FractionRing B) (FractionRing T) :=
    rootStage_fractionRing_isSeparable A D p t ht hdim hsep n _ _
  have hinjective := tensorProduct_injective_of_flat_of_localized_separable
    B R T (FractionRing B) (FractionRing R) (FractionRing T) (FractionRing C)
    (nonZeroDivisors B) (IsScalarTower.toAlgHom B R (FractionRing R))
    (IsScalarTower.toAlgHom B T (FractionRing T))
    (IsFractionRing.injective R _) (IsFractionRing.injective T _)
  have heq : ∀ x : R ⊗[B] T,
      Algebra.TensorProduct.productMap
        ((IsScalarTower.toAlgHom B (FractionRing R) (FractionRing C)).comp
          (IsScalarTower.toAlgHom B R (FractionRing R)))
        ((IsScalarTower.toAlgHom B (FractionRing T) (FractionRing C)).comp
          (IsScalarTower.toAlgHom B T (FractionRing T))) x =
      algebraMap C (FractionRing C) (perfectBaseChangeMap A D p t hbase n x) := by
    intro x
    induction x using TensorProduct.inductionOn with
    | tmul r d =>
      simp only [Algebra.TensorProduct.productMap_apply_tmul, AlgHom.comp_apply,
        IsScalarTower.coe_toAlgHom', ← IsScalarTower.algebraMap_apply]
      change algebraMap R (FractionRing C) r * algebraMap T (FractionRing C) d =
        algebraMap C (FractionRing C) (towerToPerfect A C t p r * (d : C))
      rw [map_mul, IsScalarTower.algebraMap_apply R C (FractionRing C),
        IsScalarTower.algebraMap_apply T C (FractionRing C)]
      rfl
    | add x y hx hy => simp only [map_add, hx, hy]
  intro x y hxy
  apply hinjective
  rw [heq, heq, hxy]

end Injectivity

/-- 自然な写像の像は、既に定義した近似部分代数に等しい。単射性は仮定しない。 -/
theorem perfectBaseChangeMap_range (n : ℕ) :
    (perfectBaseChangeMap A D p t hbase n).range =
      perfectionApproximation D p (Tower A t p) n := by
  rw [perfectBaseChangeMap, tensorProduct_range_eq_adjoin]
  unfold perfectionApproximation
  change Algebra.adjoin (Tower A t p) (Set.range (rootStageInclusion A D p t hbase n)) =
    Algebra.adjoin (Tower A t p) (Set.range (perfectionRootHom D p n))
  congr 1
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact y.property
  · rintro ⟨y, rfl⟩
    exact ⟨⟨perfectionRootHom D p n y, ⟨y, rfl⟩⟩, rfl⟩

/-- 像に値域を制限した、テンソル積から近似部分代数への全射。 -/
noncomputable def perfectBaseChangeSurjection (n : ℕ) :
    Tower A t p ⊗[TowerStage A t p n] perfectionRootStage D p n →ₐ[Tower A t p]
      perfectionApproximation D p (Tower A t p) n :=
  (perfectBaseChangeMap A D p t hbase n).codRestrict _ fun x ↦ by
    rw [← perfectBaseChangeMap_range A D p t hbase n]
    exact AlgHom.mem_range_self _ x

/-- 値域を制限した写像は全射である。 -/
theorem perfectBaseChangeSurjection_surjective (n : ℕ) :
    Function.Surjective (perfectBaseChangeSurjection A D p t hbase n) := by
  rintro ⟨x, hx⟩
  rw [← perfectBaseChangeMap_range A D p t hbase n] at hx
  obtain ⟨y, hy⟩ := hx
  exact ⟨y, Subtype.ext hy⟩

/-- 論文の近似環 `B_q` は `Λ ⊗_{A_n} D^{1/pⁿ}` と同型。
補題2.2の剰余体の一致から基底の剰余体の完全性を移し、
自然な写像の単射性と、近似部分代数への全射性を合わせる。 -/
noncomputable def perfectBaseChangeEquiv [IsDomain D] [IsLocalRing D]
    [IsRegularLocalRing A] [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    [CharP (IsLocalRing.ResidueField D) p] [PerfectField (IsLocalRing.ResidueField D)]
    (ht : Ideal.span (Set.range t) = IsLocalRing.maximalIdeal A)
    (hdim : ringKrullDim A = h) (hinj : Function.Injective (algebraMap A D))
    (hres : Function.Surjective ((IsLocalRing.residue D).comp (algebraMap A D)))
    (hsep : ∀ d : D, ((minpoly A d).map (algebraMap A (FractionRing A))).Separable)
    (n : ℕ) :
    Tower A t p ⊗[TowerStage A t p n] perfectionRootStage D p n ≃ₐ[Tower A t p]
      perfectionApproximation D p (Tower A t p) n := by
  let e := residueFieldEquiv_of_surjective (R := A) D hres
  let : CharP (IsLocalRing.ResidueField A) p := e.toRingHom.charP e.injective p
  let : PerfectField (IsLocalRing.ResidueField A) := PerfectField.of_ringEquiv e.symm
  apply AlgEquiv.ofBijective (perfectBaseChangeSurjection A D p t hbase n)
  refine ⟨?_, perfectBaseChangeSurjection_surjective A D p t hbase n⟩
  intro x y hxy
  apply perfectBaseChangeMap_injective A D p t hbase ht hdim hinj hsep n
  exact congrArg Subtype.val hxy

/-- 近似環との同型を perfection に入れると、元の積写像に戻る。 -/
@[simp] theorem perfectBaseChangeEquiv_coe [IsDomain D] [IsLocalRing D]
    [IsRegularLocalRing A] [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    [CharP (IsLocalRing.ResidueField D) p] [PerfectField (IsLocalRing.ResidueField D)]
    (ht : Ideal.span (Set.range t) = IsLocalRing.maximalIdeal A)
    (hdim : ringKrullDim A = h) (hinj : Function.Injective (algebraMap A D))
    (hres : Function.Surjective ((IsLocalRing.residue D).comp (algebraMap A D)))
    (hsep : ∀ d : D, ((minpoly A d).map (algebraMap A (FractionRing A))).Separable)
    (n : ℕ) (x : Tower A t p ⊗[TowerStage A t p n] perfectionRootStage D p n) :
    (perfectBaseChangeEquiv A D p t hbase ht hdim hinj hres hsep n x : PerfectClosure D p) =
      perfectBaseChangeMap A D p t hbase n x := by rfl

end SerrePositivity.Section2
