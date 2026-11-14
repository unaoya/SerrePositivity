module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.BhattScholze.Almost.Lemma103
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.DerivedPurity
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.CompletedBaseChange
public import SerrePositivity.CategoryTheory.ExactDerivedTStructure
public import SerrePositivity.BhattScholze.PerfectoidIdeal.Basic
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.CompletedTensorVanishing
public import SerrePositivity.CommutativeAlgebra.Almost.Quotient

/-!
# perfectoid 化の核に関する almost 数学（BS 著者版 Proposition 10.2、BS 著者版 Remark 10.7）

## 概要
核の conormal の導来完備化は零、核の mod pⁿ 像は冪等、核で零化される導来完備加群は拡大で閉じる。
核の conormal の完備化の消滅と核の冪に関する等式は、BS 著者版 Lemma 10.3 から Remark 10.7 の mod pⁿ の冪等性を導く中間結果である。

## 方針
BS 著者版 Lemma 10.3 から conormal を消し、冪等性と拡大閉性を出す。

## 規約
BS 著者版 Proposition 10.4 の一般の almost 同型の主張全体は、このファイルの結論には含めない。

## 使われ方
CLMST の almost Tor。
-/

universe u

/-! ## perfectoid イデアルの mod pᴺ の像

perfectoid イデアルを核の定義のまま `p^N` を法とした環へ写し（`perfectoidIdealMod`）、その零化条件と元の環の条件を商環の作用で比べる。局所化での零・同型の判定と、共通の p 冪の零化も与える。像イデアルの冪等性は下の BS 著者版 Remark 10.7 の節で示す。
-/

@[expose] public noncomputable section PerfectoidIdealModPart

namespace SerrePositivity.BhattScholze
open _root_.CategoryTheory _root_.CategoryTheory.Limits

variable (R : Type u) [CommRing R] (p : ℕ) [Fact p.Prime]
    (hR : IsIntegralPerfectoid R p) (g : R)

/-- p^N を法とした環での perfectoid ideal の像。
元のイデアルは普遍 perfectoid 化への写像の核であり、根生成イデアルに置き換えない。 -/
abbrev Almost.perfectoidIdealMod (N : ℕ) : Ideal (R ⧸ Ideal.span {(p : R) ^ N}) :=
  (_root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal R p hR g).map (Ideal.Quotient.mk (Ideal.span {(p : R) ^ N}))

/-- p^N により零化される加群の商環作用で、perfectoid ideal の零化条件は変わらない。 -/
theorem Almost.perfectoidIdealMod_annihilates_iff (N : ℕ) (M : ModuleCat.{u} R)
    (hM : _root_.SerrePositivity.Almost.IsAlmostZero (Ideal.span {(p : R) ^ N}) M) :
    let _ := _root_.SerrePositivity.Almost.quotientModule (Ideal.span {(p : R) ^ N}) M hM
    _root_.SerrePositivity.Almost.IsAlmostZero (_root_.SerrePositivity.BhattScholze.Almost.perfectoidIdealMod R p hR g N) M ↔
      _root_.SerrePositivity.Almost.IsAlmostZero (_root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal R p hR g) M :=
  _root_.SerrePositivity.Almost.isAlmostZero_quotient_iff (Ideal.span {(p : R) ^ N}) M
    (_root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal R p hR g) hM

/-- mod p^N の像イデアルの冪等性が供給されれば、almost 圏の零性と元の kernel による零化が一致。
冪等性をこの接続の結論に隠さない。 -/
theorem Almost.isZero_perfectoidIdealMod_localization_iff (N : ℕ)
    [Fact (_root_.SerrePositivity.BhattScholze.Almost.perfectoidIdealMod R p hR g N * _root_.SerrePositivity.BhattScholze.Almost.perfectoidIdealMod R p hR g N =
      _root_.SerrePositivity.BhattScholze.Almost.perfectoidIdealMod R p hR g N)]
    (M : ModuleCat.{u} R) (hM : _root_.SerrePositivity.Almost.IsAlmostZero (Ideal.span {(p : R) ^ N}) M) :
    let _ := _root_.SerrePositivity.Almost.quotientModule (Ideal.span {(p : R) ^ N}) M hM
    IsZero ((_root_.SerrePositivity.Almost.localization (_root_.SerrePositivity.BhattScholze.Almost.perfectoidIdealMod R p hR g N)).obj
      (ModuleCat.of (R ⧸ Ideal.span {(p : R) ^ N}) M)) ↔
      _root_.SerrePositivity.Almost.IsAlmostZero (_root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal R p hR g) M :=
  _root_.SerrePositivity.Almost.isZero_quotient_localization_obj_iff (Ideal.span {(p : R) ^ N})
    (_root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal R p hR g) M hM

/-- mod p^N の almost 圏で線形写像が同型となる条件を、元の環の核・余核の零化条件へ移す。 -/
theorem Almost.isIso_perfectoidIdealMod_localization_iff (N : ℕ)
    [Fact (_root_.SerrePositivity.BhattScholze.Almost.perfectoidIdealMod R p hR g N * _root_.SerrePositivity.BhattScholze.Almost.perfectoidIdealMod R p hR g N =
      _root_.SerrePositivity.BhattScholze.Almost.perfectoidIdealMod R p hR g N)]
    {M M' : ModuleCat.{u} R}
    (hM : _root_.SerrePositivity.Almost.IsAlmostZero (Ideal.span {(p : R) ^ N}) M)
    (hM' : _root_.SerrePositivity.Almost.IsAlmostZero (Ideal.span {(p : R) ^ N}) M') (f : M ⟶ M') :
    let _ := _root_.SerrePositivity.Almost.quotientModule (Ideal.span {(p : R) ^ N}) M hM
    let _ := _root_.SerrePositivity.Almost.quotientModule (Ideal.span {(p : R) ^ N}) M' hM'
    IsIso ((_root_.SerrePositivity.Almost.localization (_root_.SerrePositivity.BhattScholze.Almost.perfectoidIdealMod R p hR g N)).map
      (ModuleCat.ofHom (_root_.SerrePositivity.Almost.quotientLinearMap (Ideal.span {(p : R) ^ N}) hM hM' f.hom))) ↔
      _root_.SerrePositivity.Almost.IsAlmostIso (_root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal R p hR g) f.hom :=
  _root_.SerrePositivity.Almost.isIso_quotient_localization_map_iff (Ideal.span {(p : R) ^ N})
    (_root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal R p hR g) hM hM' f

omit [Fact p.Prime] in
/-- p が J に属すれば、一様な J 冪ねじれの二つの加群を同じ p の冪で零化できる。
mod p^N の almost 圏へ移す指数は仮定ではなく、各加群の冪ねじれから供給する。 -/
theorem Almost.exists_common_p_pow_annihilates (J : Ideal R) (hp : (p : R) ∈ J)
    (M M' : ModuleCat.{u} R) (hM : _root_.SerrePositivity.IsPowTorsion J M) (hM' : _root_.SerrePositivity.IsPowTorsion J M') :
    ∃ N : ℕ, _root_.SerrePositivity.Almost.IsAlmostZero (Ideal.span {(p : R) ^ N}) M ∧
      _root_.SerrePositivity.Almost.IsAlmostZero (Ideal.span {(p : R) ^ N}) M' := by
  obtain ⟨n, hn⟩ := hM
  obtain ⟨n', hn'⟩ := hM'
  refine ⟨n + n', ?_, ?_⟩
  · change Ideal.span {(p : R) ^ (n + n')} ≤ Module.annihilator R M
    rw [Ideal.span_singleton_le_iff_mem, Module.mem_annihilator]
    intro m
    rw [pow_add, mul_smul]
    exact hn (a := ⟨(p : R) ^ n, Ideal.pow_mem_pow hp n⟩)
  · change Ideal.span {(p : R) ^ (n + n')} ≤ Module.annihilator R M'
    rw [Ideal.span_singleton_le_iff_mem, Module.mem_annihilator]
    intro m
    rw [Nat.add_comm n n', pow_add, mul_smul]
    exact hn' (a := ⟨(p : R) ^ n', Ideal.pow_mem_pow hp n'⟩)

end SerrePositivity.BhattScholze

end PerfectoidIdealModPart


/-! ## perfectoid 化の核の conormal の導来完備化

## 概要
核 K の通常の conormal 加群 K/K² は p 作用が可逆であり、その導来 p 完備化は零である。
## 方針
BS 著者版 Lemma 10.3 の商自己積を Koszul 錐へ移し、H⁻² の消滅から Tor₁ 上の p 単射性を得る。
## 規約
conormal の完備化と、導来自己テンソルの完備化を区別する。
## 使われ方
BS 著者版 Remark 10.7（印刷 p.80）の mod p 冪冪等性の中間結果を明示する。
-/

@[expose] public noncomputable section PerfectoidIdealConormalCompletion

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.HomologicalComplex _root_.SerrePositivity.DerivedCompletion
attribute [local instance] HasDerivedCategory.standard
variable (R : Type u) [CommRing R] (p : ℕ) [Fact p.Prime]
    (hR : IsIntegralPerfectoid R p) (g : R)

/--
## 概要
perfectoid 化の核 K の conormal 加群 K/K² 上の p 作用は全単射である。
## 方針
商自己積の完備化同型の Koszul 還元から単射性を得て、既存の Tor₁ 可除性と合成する。
## 規約
通常の conormal 加群に関する主張であり、p ねじれなしを追加仮定しない。
## 使われ方
BS 著者版 Remark 10.7（印刷 p.80）の導来完備化消滅を証明する。
-/
theorem Almost.perfectoidIdeal_conormal_smul_bijective :
    Function.Bijective (fun x : (_root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal R p hR g).Cotangent => (p : R) • x) := by
  let I := _root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal R p hR g
  let Q := ModuleCat.of R (R ⧸ I)
  let μ := _root_.SerrePositivity.boundedAboveDerivedAlgebraMul (R := R) (R ⧸ I)
  have hμ := (_root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal_lemma103 R p hR g).2.1
  have hk : IsIso ((derivedScalarConeFunctor R (p : R)).map μ.hom) := by
    have hh := derivedScalarCone_map_isIso_of_completion R (p : R) μ.hom hμ 1
    rw [_root_.pow_one] at hh
    exact hh
  let L := (CochainComplex.singleFunctor (ModuleCat R) 0).obj Q
  have hl (i : ℤ) (hi : i ≠ 0) : IsZero (L.homology i) :=
    (_root_.SerrePositivity.derivedSingleHomology_isZero Q i hi).of_iso
      ((DerivedCategory.homologyFunctorFactors (ModuleCat R) i).app L).symm
  have hzL : IsZero (((_root_.SerrePositivity.scalarConeFunctor (p : R)).obj L).homology (-2)) :=
    (_root_.SerrePositivity.Cone.exact₃ (_root_.SerrePositivity.smulId (p : R) L) (-2) (-1) (by omega)).isZero_of_both_isZero
      (hl (-2) (by omega)) (hl (-1) (by omega))
  have hzY : IsZero ((DerivedCategory.homologyFunctor (ModuleCat R) (-2)).obj
      ((derivedScalarConeFunctor R (p : R)).obj
        ((_root_.SerrePositivity.boundedAboveDerivedSingleFunctor.obj Q).obj))) := hzL.of_iso
    ((DerivedCategory.homologyFunctor (ModuleCat R) (-2)).mapIso
      ((derivedScalarConeComparison R (p : R)).app L) ≪≫
      (DerivedCategory.homologyFunctorFactors (ModuleCat R) (-2)).app
        ((_root_.SerrePositivity.scalarConeFunctor (p : R)).obj L))
  have hzX := hzY.of_iso ((DerivedCategory.homologyFunctor (ModuleCat R) (-2)).mapIso
    (asIso ((derivedScalarConeFunctor R (p : R)).map μ.hom)))
  have hinj := derived_homology_smul_injective_of_scalarCone_isZero (p : R)
    ((_root_.SerrePositivity.boundedAboveDerivedTensorModuleFunctor Q).obj Q) (-1)
    (by simpa [_root_.SerrePositivity.boundedAboveDerivedTensorModuleFunctor, Q] using hzX)
  let e := (((_root_.SerrePositivity.boundedAboveDerivedTensorModuleTorNatIso Q 1).app Q).toLinearEquiv).trans
    (_root_.SerrePositivity.quotientTorOneConormalEquiv R I)
  constructor
  · intro x y hxy
    change (p : R) • x = (p : R) • y at hxy
    apply e.symm.injective
    apply hinj
    change (p : R) • e.symm x = (p : R) • e.symm y
    rw [← e.symm.map_smul, ← e.symm.map_smul, hxy]
  · exact (_root_.SerrePositivity.quotientTorOne_smul_surjective_iff_conormal R I (p : R)).mp
      (quotientTorOne_smul_surjective_of_completed_mul_isIso (p : R) I hμ)

/--
## 概要
perfectoid 化の核 K の通常の conormal 加群 K/K² の導来 p 完備化は零である。
## 方針
p 作用の全単射性を実完備化へ移す。その各ホモロジーは導来完備かつ p 可除なので零となる。
## 規約
G2 の元の完備化関手を degree zero の conormal 加群へ適用する。
## 使われ方
mod pⁿ の像の冪等性を導く中間結果を公開する。
-/
theorem Almost.perfectoidIdeal_conormal_completion_isZero :
    IsZero ((derivedComplexCompletionFunctor R (p : R)).obj
      ((DerivedCategory.singleFunctor (ModuleCat R) 0).obj
        (ModuleCat.of R (_root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal R p hR g).Cotangent))) := by
  let M := ModuleCat.of R (_root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal R p hR g).Cotangent
  let X := (DerivedCategory.singleFunctor (ModuleCat R) 0).obj M
  let F := derivedComplexCompletionFunctor R (p : R)
  have hM : IsIso ((p : R) • 𝟙 M) := (ConcreteCategory.isIso_iff_bijective _).mpr
    (_root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal_conormal_smul_bijective R p hR g)
  have hX : IsIso ((p : R) • 𝟙 X) := by
    have hh := (DerivedCategory.singleFunctor (ModuleCat R) 0).map_isIso ((p : R) • 𝟙 M)
    simpa only [Functor.map_smul, CategoryTheory.Functor.map_id] using hh
  have hF : IsIso ((p : R) • 𝟙 (F.obj X)) := by
    have hh := F.map_isIso ((p : R) • 𝟙 X)
    rwa [derivedCompletion_map_scalar_id] at hh
  apply (_root_.SerrePositivity.derived_isZero_iff_homology _).mpr
  intro i
  have hH : IsIso ((p : R) • 𝟙 ((DerivedCategory.homologyFunctor (ModuleCat R) i).obj
      (F.obj X))) := by
    have hh := (DerivedCategory.homologyFunctor (ModuleCat R) i).map_isIso
      ((p : R) • 𝟙 (F.obj X))
    simpa only [Functor.map_smul, CategoryTheory.Functor.map_id] using hh
  exact isZero_of_complete_of_smul_surjective (p : R) _
    (isComplete_homology_isModuleComplete R (p : R) (F.obj X)
      (derivedComplexCompletionFunctor_isComplete R (p : R) X) i)
    ((ConcreteCategory.isIso_iff_bijective _).mp hH).surjective

/--
## 概要
perfectoid 化の核 K の通常の conormal 加群を p で割ると零加群になる。
## 方針
p 作用の全射性で代表を p 倍に書き、通常の商写像が p 倍を消すことを使う。
## 規約
完備化後の H⁰ だけでなく、元の通常の conormal の mod p 商について主張する。
## 使われ方
BS 著者版 Remark 10.7（印刷 p.80）の K=K²+pK へ移る中間結果である。
-/
theorem Almost.perfectoidIdeal_conormal_mod_p_isZero :
    IsZero (modulePowerReduction (p : R)
      (ModuleCat.of R (_root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal R p hR g).Cotangent) 1) := by
  let M := ModuleCat.of R (_root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal R p hR g).Cotangent
  apply ModuleCat.isZero_iff_subsingleton.mpr
  apply subsingleton_of_forall_eq 0
  intro x
  obtain ⟨m, rfl⟩ := (ModuleCat.epi_iff_surjective (modulePowerReductionMap (p : R) M 1)).mp
    (inferInstance) x
  obtain ⟨y, hy⟩ := (_root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal_conormal_smul_bijective R p hR g).surjective m
  change (modulePowerReductionMap (p : R) M 1).hom m = 0
  rw [← hy, map_smul]
  simpa only [_root_.pow_one] using
    modulePowerReduction_pow_smul_zero (p : R) M 1
      ((modulePowerReductionMap (p : R) M 1) y)

end SerrePositivity.BhattScholze

end PerfectoidIdealConormalCompletion

/-! ## BS 著者版 Remark 10.7 の mod p 冪の冪等性

## 概要
perfectoid 化の核 K の mod pⁿ 像は冪等である（BS 著者版 Remark 10.7、印刷 p.80）。
## 方針
BS 著者版 Lemma 10.3 の実自己積から既存の Tor₁・conormal 比較を通じて K/K² の p 可除性を得る。
それを反復し K=K²+pⁿK を証明して、既存の像イデアルの冪等性判定を使う。
## 規約
CLMST.Almost の既存の像イデアルの略記だけを利用し、入力引用は使わない。
## 使われ方
CLMST の BasicSetup と同じ署名で冪等性を渡す。BasicSetup 自体は編集しない。
-/

@[expose] public noncomputable section PerfectoidIdealIdempotent

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze
open _root_.CategoryTheory _root_.SerrePositivity.DerivedCompletion
attribute [local instance] HasDerivedCategory.standard
variable (R : Type u) [CommRing R] (p : ℕ) [Fact p.Prime]
    (hR : IsIntegralPerfectoid R p) (g : R)

/--
## 概要
perfectoid 化の核 K の conormal 加群 K/K² は全 pⁿ で可除である。
## 方針
BS 著者版 Lemma 10.3 の商自己積から実 Tor₁ の p 可除性を得て既存の conormal 比較で移し、反復する。
## 規約
通常の conormal 加群を使い、p ねじれの有無を仮定しない。
## 使われ方
BS 著者版 Remark 10.7（印刷 p.80）の冪等性の計算に使う。
-/
theorem Almost.perfectoidIdeal_conormal_pow_smul_surjective (n : ℕ) :
    Function.Surjective
      (fun x : (_root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal R p hR g).Cotangent => (p : R) ^ n • x) := by
  have h := (_root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal_conormal_smul_bijective R p hR g).surjective
  induction n with
  | zero =>
    intro x
    exact ⟨x, by simp⟩
  | succ n ih =>
    intro x
    obtain ⟨y, hy⟩ := ih x
    obtain ⟨z, hz⟩ := h y
    refine ⟨z, ?_⟩
    change (p : R) ^ n • y = x at hy
    change (p : R) • z = y at hz
    change (p : R) ^ (n + 1) • z = x
    rw [pow_succ, mul_smul, hz, hy]

/--
## 概要
perfectoid 化の核 K は K²+pⁿK に等しい。n=1 は K=K²+pK を与える。
## 方針
conormal 加群の pⁿ 可除性の原像を K に持ち上げ、差が K² に属することを使う。
## 規約
pⁿK は span{pⁿ} と K のイデアル積で明示する。
## 使われ方
mod pⁿ の像の冪等性の中間等式である。
-/
theorem Almost.perfectoidIdeal_eq_square_sup_pow_mul (n : ℕ) :
    let K := _root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal R p hR g
    K = K * K ⊔ Ideal.span {(p : R) ^ n} * K := by
  let K := _root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal R p hR g
  apply le_antisymm
  · intro x hx
    obtain ⟨y, hy⟩ := _root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal_conormal_pow_smul_surjective R p hR g n
      (K.toCotangent ⟨x, hx⟩)
    obtain ⟨z, rfl⟩ := K.toCotangent_surjective y
    change (p : R) ^ n • K.toCotangent z = K.toCotangent ⟨x, hx⟩ at hy
    have hz : K.toCotangent (⟨x, hx⟩ - (p : R) ^ n • z) = 0 := by
      rw [map_sub, map_smul, hy, sub_self]
    have hmem : x - (p : R) ^ n * (z : R) ∈ K * K := by
      have hz₂ := (K.toCotangent_eq_zero _).mp hz
      change x - (p : R) ^ n * (z : R) ∈ K ^ 2 at hz₂
      simpa only [pow_two] using hz₂
    have hpz : (p : R) ^ n * (z : R) ∈ Ideal.span {(p : R) ^ n} * K :=
      Ideal.mul_mem_mul (Ideal.mem_span_singleton_self _) z.property
    exact Submodule.mem_sup.mpr ⟨_, hmem, _, hpz, sub_add_cancel _ _⟩
  · exact sup_le Ideal.mul_le_left Ideal.mul_le_right

/--
## 概要
単項商の perfectoid 化の核の mod pᴺ 像は冪等である（BS 著者版 Remark 10.7 の mod pⁿ 像の冪等性の単項 J の場合）。
## 方針
実商自己積の同型性から、既存の Tor₁・conormal・像イデアルの冪等性判定を適用する。
## 規約
BhattScholze.perfectoidIdealMod_idempotent と同じ署名を保持し、N=0 も含む。
## 使われ方
既存の入力引用を使わずに CLMST へ渡す証明済み入口である。
-/
theorem Almost.perfectoidIdealMod_idempotent (N : ℕ) :
    _root_.SerrePositivity.BhattScholze.Almost.perfectoidIdealMod R p hR g N * _root_.SerrePositivity.BhattScholze.Almost.perfectoidIdealMod R p hR g N =
      _root_.SerrePositivity.BhattScholze.Almost.perfectoidIdealMod R p hR g N :=
  _root_.SerrePositivity.ideal_mod_power_idempotent_of_conormal_surjective (p : R) (_root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal R p hR g)
    (_root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal_conormal_smul_bijective R p hR g).surjective N

end SerrePositivity.BhattScholze

end PerfectoidIdealIdempotent

/-! ## BS 著者版 Proposition 10.2 の導来完備 almost 零加群の拡大閉性

## 概要
perfectoid 化の核で零化される導来完備加群は拡大で閉じる（BS 著者版 Proposition 10.2、印刷 p.78）。
## 方針
BS 著者版 Proposition 10.4（印刷 p.79）の環版を使う。商加群の作用から完備テンソルの消滅を得て、
短完全列の三角形で中央へ移し、その H⁰ の商加群構造を復元する。
## 規約
既存の perfectoidIdeal、IsAlmostZero、G2 の実完備導来 tensor を使う。
## 使われ方
CLMST の Tor 比較 が指定した正確な署名の拡大閉性を供給する。
-/

@[expose] public noncomputable section PerfectoidAlmostExtension

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.MonoidalCategory _root_.SerrePositivity.DerivedCompletion
open _root_.SerrePositivity.Almost
attribute [local instance] HasDerivedCategory.standard
variable {R : Type u} [CommRing R]

private lemma Almost.annihilates_of_completedTensor_zero (a : R) (I : Ideal R)
    (M : ModuleCat.{u} R) (hM : IsModuleComplete R a M)
    (hz : IsZero ((derivedComplexCompletionFunctor R a).obj
      ((_root_.SerrePositivity.boundedAboveDerivedTensorModuleFunctor (ModuleCat.of R I)).obj M))) :
    IsAlmostZero I M := by
  let F := derivedComplexCompletionFunctor R a
  let Md := _root_.SerrePositivity.boundedAboveDerivedSingleFunctor.obj M
  let Id := _root_.SerrePositivity.boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R I)
  let Qd := _root_.SerrePositivity.boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R (R ⧸ I))
  let S := ModuleCat.shortComplexOfCompEqZero I.subtype I.mkQ
    (LinearMap.exact_subtype_mkQ I).linearMap_comp_eq_zero
  have hS : S.ShortExact := ModuleCat.shortComplex_shortExact S
    (LinearMap.exact_subtype_mkQ I) I.injective_subtype I.mkQ_surjective
  have hz' : IsZero (F.obj (Md ⊗ Id).obj) := hz.of_iso
    (F.mapIso (DerivedCategory.Minus.ι.mapIso (β_ Md Id)))
  have hg : IsIso (F.map ((_root_.SerrePositivity.boundedAboveDerivedTensorModuleFunctor M).map S.g)) :=
    completedTensor_shortExact_rightMap_isIso_of_isZero a M S hS hz'
  have := hg
  let eR : F.obj ((_root_.SerrePositivity.boundedAboveDerivedTensorModuleFunctor M).obj (ModuleCat.of R R)) ≅
      Md.obj :=
    F.mapIso (DerivedCategory.Minus.ι.mapIso (ρ_ Md)) ≪≫
      (derivedComplexCompletionUnitIso R a Md.obj hM).symm
  let e : Md.obj ≅ F.obj (Qd ⊗ Md).obj :=
    eR.symm ≪≫ asIso (F.map ((_root_.SerrePositivity.boundedAboveDerivedTensorModuleFunctor M).map S.g)) ≪≫
      F.mapIso (DerivedCategory.Minus.ι.mapIso (β_ Md Qd))
  let eH := ((DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat R) 0).app M).symm ≪≫
    (DerivedCategory.homologyFunctor (ModuleCat R) 0).mapIso e
  let q := Ideal.Quotient.mk I
  let eQ := completedBaseChangeTensorRestrictionHomologyIso q a Md 0
  let eM := eH ≪≫ eQ.symm
  apply IsAlmostZero.of_equiv eM.toLinearEquiv.symm
  apply IsAlmostZero.iff_smul_eq_zero.mpr
  intro r hr m
  change (Ideal.Quotient.mk I r) • m = 0
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr hr, zero_smul]

/--
## 概要
perfectoid 化の核 K が M を零化すれば、K⊗̂ᴸM は零である（BS 著者版 Proposition 10.4 の同値の順方向で単項 J と加群の場合）。
## 方針
既存の商環作用で M を R/K 加群とし、BS 著者版 Lemma 10.3 の混合積消滅と作用 retract を使う。
## 規約
この方向には M の完備性・平坦性・有限性は必要ない。
## 使われ方
短完全列の両端を完備テンソルで消し、BS 著者版 Proposition 10.2 の拡大閉性に使う。
-/
theorem Almost.perfectoidIdeal_completedTensor_isZero_of_isAlmostZero
    (R : Type u) [CommRing R] (p : ℕ) [Fact p.Prime]
    (hR : _root_.SerrePositivity.IsIntegralPerfectoid R p) (g : R)
    (M : ModuleCat.{u} R) (hM : IsAlmostZero (_root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal R p hR g) M) :
    IsZero ((derivedComplexCompletionFunctor R (p : R)).obj
      ((_root_.SerrePositivity.boundedAboveDerivedTensorModuleFunctor
        (ModuleCat.of R (_root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal R p hR g))).obj M)) := by
  let K := _root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal R p hR g
  let := quotientModule K M hM
  let := quotientModule_scalarTower K M hM
  exact completedTensor_isZero_of_algebraModule R (p : R) (R ⧸ K) M
    (_root_.SerrePositivity.boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R K))
    (_root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal_lemma103 R p hR g).2.2

/--
## 概要
導来 p 完備加群 M について、K⊗̂ᴸM が零なら
perfectoid 化の核 K は M を零化する（BS 著者版 Proposition 10.4 の逆方向の単項 J の場合）。
## 方針
K→R→R/K の tensor 三角形から M≅(R/K)⊗̂ᴸM を得て、実 H⁰ の商環作用を移す。
## 規約
導来完備性を標準完備化単位で使い、古典的完備化で代用しない。
## 使われ方
BS 著者版 Proposition 10.2 の中央加群のテンソル消滅から、元の零化条件を復元する。
-/
theorem Almost.perfectoidIdeal_isAlmostZero_of_completedTensor_isZero
    (R : Type u) [CommRing R] (p : ℕ) [Fact p.Prime]
    (hR : _root_.SerrePositivity.IsIntegralPerfectoid R p) (g : R)
    (M : ModuleCat.{u} R) (hM : IsModuleComplete R (p : R) M)
    (hz : IsZero ((derivedComplexCompletionFunctor R (p : R)).obj
      ((_root_.SerrePositivity.boundedAboveDerivedTensorModuleFunctor
        (ModuleCat.of R (_root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal R p hR g))).obj M))) :
    IsAlmostZero (_root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal R p hR g) M :=
  _root_.SerrePositivity.BhattScholze.Almost.annihilates_of_completedTensor_zero (p : R) (_root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal R p hR g) M hM hz

-- 指定署名を保持する。両端の tensor 消滅には h₁,h₃ は不要である。
set_option linter.unusedVariables false in
/--
## 概要
perfectoid 化の核で零化される導来 p 完備加群は、導来完備加群の短完全拡大で閉じる（BS 著者版 Proposition 10.2 の拡大閉性で単項 J の場合）。
## 方針
商加群の作用から両端の K⊗̂ᴸ− を消し、完全三角形で中央も消えることを示す。
BS 著者版 Proposition 10.4 の逆方向により、その実 H⁰ の R/K 作用から中央の零化条件を復元する。
## 規約
指定の三つの完備性引数を保持する。両端からの消滅の方向は完備性なしにも成立する。
## 使われ方
CLMST の Tor 比較 に指定された署名で渡す、証明済みの拡大閉性定理である。
-/
theorem Almost.perfectoidIdeal_isAlmostZero_extension
    (R : Type u) [CommRing R] (p : ℕ) [Fact p.Prime]
    (hR : _root_.SerrePositivity.IsIntegralPerfectoid R p) (g : R)
    (S : ShortComplex (ModuleCat.{u} R)) (hS : S.ShortExact)
    (h₁ : IsModuleComplete R (p : R) S.X₁) (h₂ : IsModuleComplete R (p : R) S.X₂)
    (h₃ : IsModuleComplete R (p : R) S.X₃)
    (hX₁ : IsAlmostZero (_root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal R p hR g) S.X₁)
    (hX₃ : IsAlmostZero (_root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal R p hR g) S.X₃) :
    IsAlmostZero (_root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal R p hR g) S.X₂ := by
  apply _root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal_isAlmostZero_of_completedTensor_isZero R p hR g S.X₂ h₂
  exact completedTensor_isZero_of_shortExact (p : R)
    (ModuleCat.of R (_root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal R p hR g)) S hS
    (_root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal_completedTensor_isZero_of_isAlmostZero R p hR g S.X₁ hX₁)
    (_root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal_completedTensor_isZero_of_isAlmostZero R p hR g S.X₃ hX₃)

end SerrePositivity.BhattScholze

end PerfectoidAlmostExtension

/-! ## perfectoid イデアルの almost 判定の公開入口

## 概要
BS 著者版 Lemma 10.3（印刷 pp.78–79）、BS 著者版 Remark 10.7（印刷 p.80）の冪等性、
BS 著者版 Proposition 10.2（印刷 p.78）の導来完備 almost 零加群の拡大閉性をまとめる。
## 方針
既存 B3・B4 と、完全 prism による実完備導来 tensor の一般定理を再利用する。
## 規約
核と mod p 冪像の既存定義を保持し、全定理は追加の引用なしに証明されている。
## 使われ方
ルートの一つの import と、CLMST の Tor 比較・CLMST への証明済み公開定理の受渡しに使う。
-/

@[expose] public noncomputable section PerfectoidAlmostModCategoryPart

namespace SerrePositivity.BhattScholze
open _root_.CategoryTheory

variable (R : Type u) [CommRing R] (p : ℕ) [Fact p.Prime]
    (hR : IsIntegralPerfectoid R p) (g : R)

/-- mod p^N の全加群の perfectoid almost 圏。
文献入力の冪等性を定義の局所的な instance として供給する。 -/
abbrev Almost.perfectoidAlmostModCategory (N : ℕ) :=
  letI : Fact (_root_.SerrePositivity.BhattScholze.Almost.perfectoidIdealMod R p hR g N * _root_.SerrePositivity.BhattScholze.Almost.perfectoidIdealMod R p hR g N =
      _root_.SerrePositivity.BhattScholze.Almost.perfectoidIdealMod R p hR g N) := ⟨_root_.SerrePositivity.BhattScholze.Almost.perfectoidIdealMod_idempotent R p hR g N⟩
  _root_.SerrePositivity.Almost.ModuleCategory (_root_.SerrePositivity.BhattScholze.Almost.perfectoidIdealMod R p hR g N)

/-- mod p^N の加群から、その perfectoid almost 圏への局所化関手。
呼び出し側で冪等性の `Fact` を仮定する必要はない。 -/
abbrev Almost.perfectoidAlmostModLocalization (N : ℕ) :
    ModuleCat.{u} (R ⧸ Ideal.span {(p : R) ^ N}) ⥤ _root_.SerrePositivity.BhattScholze.Almost.perfectoidAlmostModCategory R p hR g N :=
  letI : Fact (_root_.SerrePositivity.BhattScholze.Almost.perfectoidIdealMod R p hR g N * _root_.SerrePositivity.BhattScholze.Almost.perfectoidIdealMod R p hR g N =
      _root_.SerrePositivity.BhattScholze.Almost.perfectoidIdealMod R p hR g N) := ⟨_root_.SerrePositivity.BhattScholze.Almost.perfectoidIdealMod_idempotent R p hR g N⟩
  _root_.SerrePositivity.Almost.localization (_root_.SerrePositivity.BhattScholze.Almost.perfectoidIdealMod R p hR g N)

/-- 明示的な冪等性の証拠を置いた場合、名前付き局所化は既存の局所化と定義上同じ。 -/
theorem Almost.perfectoidAlmostModLocalization_eq (N : ℕ)
    [Fact (_root_.SerrePositivity.BhattScholze.Almost.perfectoidIdealMod R p hR g N * _root_.SerrePositivity.BhattScholze.Almost.perfectoidIdealMod R p hR g N =
      _root_.SerrePositivity.BhattScholze.Almost.perfectoidIdealMod R p hR g N)] :
    _root_.SerrePositivity.BhattScholze.Almost.perfectoidAlmostModLocalization R p hR g N =
      _root_.SerrePositivity.Almost.localization (_root_.SerrePositivity.BhattScholze.Almost.perfectoidIdealMod R p hR g N) := rfl

end SerrePositivity.BhattScholze

end PerfectoidAlmostModCategoryPart

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite BS19 "Prop 10.2" (partial := special) "本体は単項 J=(g) の perfectoid 核で、導来完備加群の短完全拡大での閉性のみ（sorry 0）。核・余核での閉性と almost 圏 (R/J)_perfd 加群との同値は未。使用先は CLMST ／ DOC1 照合（11-07、Codex が型で確認）：項目そのものではないので宣言の列から外したもの：completedTensor_isZero_of_shortExact（任意の元と加群についてテンソル後の零性を述べる一般補助。J-almost zero への適用は別の宣言。）；perfectoidIdeal_allModule_tor_annihilated_of_powerTorsion（p 冪ねじれ加群の仮定から一般加群の高次 Tor の零化。Prop 10.2 の拡大閉性の宣言ではない。） ／ DOC1 照合：ok 1 件"] _root_.SerrePositivity.BhattScholze.Almost.perfectoidIdeal_isAlmostZero_extension
attribute [cite BS19 "Rem 10.7" (partial := special) "本体の perfectoidIdealMod_idempotent（単項 J=(g) の perfectoid 化の核の mod pⁿ 像が冪等）は、原典 Rem 10.7 の一文「J_perfd,n は R/pⁿ の冪等イデアル」の J=(g) の場合（調整役が原典の全文で確認、11-07。前の「ずれの疑い」は誤り）。使用先は CLMST。Galois 条件の mod pⁿ 版の部分は E3 に不要 ／ DOC1 照合（11-07、Codex が型で確認）：項目そのものではないので宣言の列から外したもの：perfectoidIdeal_conormal_completion_isZero（原文は mod p^n 像の冪等性等を述べる。conormal の主張は別で、Lemma 10.3 の応用。）；perfectoidIdeal_eq_square_sup_pow_mul（核 K について K=K²+p^nK。原文の mod p^n 像の冪等性を出す補助で、原文の結論は perfectoid） ／ DOC1 照合：ok 1 件"] _root_.SerrePositivity.BhattScholze.Almost.perfectoidIdealMod_idempotent
