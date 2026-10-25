module

public import SerrePositivity.BhattScholze.Andre.Remark715.Unconditional.PowerRootResidueSource
public import SerrePositivity.BhattScholze.Andre.MonicPrismaticQuotientDerived
public import SerrePositivity.BhattScholze.Andre.Remark715.Unconditional.PowerRootCoefficientReduction

/-!
# 元の無限根入力の実係数還元の無条件比較

## 概要
BS Rem 7.15（著者版 p.62）の元の自由 δ 源上の実導来還元を、同じ raw 残余商へ比較する。

## 方針
hpR なしの実導来評価比較と、商射の全射性による係数作用の降下を用いる。

## 規約
モニック性のみを保持し、元の自由環・raw 商を変更しない。

## 使われ方
元の A 上への係数制限と実逐次完備化の hpR 解消へ渡す。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze.Andre
open CategoryTheory CategoryTheory.Limits
attribute [local instance] HasDerivedCategory.standard
variable {A : Type u} [CommRing A] {p : ℕ} [Fact p.Prime]
variable (W : OrientedPrism p A) (hW : W.deltaStructure.IsPerfect) (f : Polynomial A)
local notation "hp" => Nat.Prime.pos (Fact.out : p.Prime)
local notation "P₀" => PowerRootPolynomial A p hp
local notation "L₀" => PowerRootUnaryFreeDeltaRing A p hp
local notation "E₀" => powerRootPolynomialDelta p hW.p_mul_injective W.deltaStructure
local notation "dP" => algebraMap A P₀ W.generator
local notation "c₀" => powerRootPrismMonicUnaryFamily (p := p) f
local notation "K₀" => Ideal.span {(p : L₀), MvPolynomial.C dP}
local notation "Q₀" => L₀ ⧸ K₀
local notation "q₀" => Ideal.Quotient.mk K₀
local notation "α₀" => deltaDivisionSourceMap E₀ dP
local notation "β₀" => deltaDivisionSourceEval E₀ c₀
local notation "ψ₀" => RingHom.comp q₀ α₀
local notation "Mα" => baseChangeScalarModule α₀
local notation "Mβ" => baseChangeScalarModule β₀
local notation "Mψ" => baseChangeScalarModule ψ₀
local notation "Res₀" => DeltaAdjoinDivisionResidue E₀ dP c₀
local notation "MRes" => CategoryTheory.Functor.obj
  (ModuleCat.restrictScalars β₀) (ModuleCat.of P₀ Res₀)
local notation "j₀" => deltaAdjoinDivisionMap E₀ dP c₀
local notation "r₀" => Ideal.Quotient.mk (deltaAdjoinDivisionResidueIdeal E₀ dP c₀)

/-- 概要：実二因子導来テンソルを実商環Q上へ基底変更した対象。
方針：実商射の全射性と係数制限のホモロジー比較で、前工程の具体的比較を商作用へ降下する。
規約：構成する各作用は元の自由 δ 源射を固定する。
使われ方：BS Rem 7.15（著者版 p.62）の元の A/(p,d) 上への比較。 -/
abbrev PowerRootPrismMonicSourceQuotientDerived_of_unconditional :=
  (boundedAboveDerivedBaseChange q₀).obj
    (boundedAboveDerivedTensor.obj
      (boundedAboveDerivedSingleFunctor.obj Mβ, boundedAboveDerivedSingleFunctor.obj Mα))

/-- 概要：raw残余商上のβを経由する源作用の、実商環への標準降下。
方針：実商射の全射性と係数制限のホモロジー比較で、前工程の具体的比較を商作用へ降下する。
規約：構成する各作用は元の自由 δ 源射を固定する。
使われ方：BS Rem 7.15（著者版 p.62）の元の A/(p,d) 上への比較。 -/
def powerRootPrismMonicSourceQuotientResidueMap_of_unconditional : Q₀ →+* Res₀ :=
  Ideal.Quotient.lift K₀ ((r₀).comp ((j₀).comp β₀)) (by
    change K₀ ≤ RingHom.ker ((r₀).comp ((j₀).comp β₀))
    apply Ideal.span_le.mpr
    intro x hx
    rcases Set.mem_insert_iff.mp hx with hx | hx
    · subst x
      change r₀ ((j₀).comp β₀ (p : L₀)) = 0
      rw [map_natCast]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr
        (Ideal.subset_span (Set.mem_insert _ _))
    · have hx := Set.mem_singleton_iff.mp hx
      subst x
      change r₀ (j₀ (β₀ (MvPolynomial.C dP))) = 0
      rw [deltaDivisionSourceEval_C]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr
        (Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))))

/-- 概要：商代表元の作用は、β、raw係数射、残余商射の合成である。
方針：実商射の全射性と係数制限のホモロジー比較で、前工程の具体的比較を商作用へ降下する。
規約：構成する各作用は元の自由 δ 源射を固定する。
使われ方：BS Rem 7.15（著者版 p.62）の元の A/(p,d) 上への比較。 -/
theorem powerRootPrismMonicSourceQuotientResidueMap_mk_of_unconditional (x : L₀) :
    powerRootPrismMonicSourceQuotientResidueMap_of_unconditional W hW f (q₀ x) =
      r₀ (j₀ (β₀ x)) := rfl

/-- 概要：商環作用をqで制限すると、前工程のβによる実L加群になる。
方針：実商射の全射性と係数制限のホモロジー比較で、前工程の具体的比較を商作用へ降下する。
規約：構成する各作用は元の自由 δ 源射を固定する。
使われ方：BS Rem 7.15（著者版 p.62）の元の A/(p,d) 上への比較。 -/
def powerRootPrismMonicSourceQuotientResidueRestrictionIso_of_unconditional :
    letI := (powerRootPrismMonicSourceQuotientResidueMap_of_unconditional W hW f).toAlgebra
    letI : Module Q₀ Res₀ := Algebra.toModule
    ((ModuleCat.restrictScalars q₀).obj (ModuleCat.of Q₀ Res₀)) ≅ MRes := by
  letI := (powerRootPrismMonicSourceQuotientResidueMap_of_unconditional W hW f).toAlgebra
  letI : Module Q₀ Res₀ := Algebra.toModule
  exact
    { hom := { hom' :=
        { toFun := fun x => x
          map_add' := fun _ _ => rfl
          map_smul' := fun r x => by
            change Res₀ at x
            change r₀ (j₀ (β₀ r)) * x = (β₀ r) • x
            rw [Algebra.smul_def]
            rfl } }
      inv := { hom' :=
        { toFun := fun x => x
          map_add' := fun _ _ => rfl
          map_smul' := fun r x => by
            change Res₀ at x
            change (β₀ r) • x = r₀ (j₀ (β₀ r)) * x
            rw [Algebra.smul_def]
            rfl } }
      hom_inv_id := by rfl
      inv_hom_id := by rfl }

/-- 概要：実商環上の基底変更を制限すると、既存の実三因子還元に一致する。
方針：実商射の全射性と係数制限のホモロジー比較で、前工程の具体的比較を商作用へ降下する。
規約：構成する各作用は元の自由 δ 源射を固定する。
使われ方：BS Rem 7.15（著者版 p.62）の元の A/(p,d) 上への比較。 -/
def powerRootPrismMonicSourceQuotientDerivedRestrictionIso_of_unconditional :
    (boundedAboveDerivedRestrictScalars q₀).obj
        (PowerRootPrismMonicSourceQuotientDerived_of_unconditional W hW f) ≅
      PowerRootPrismMonicSourceCoefficientReduced_of_unconditional W hW f :=
  (boundedAboveDerivedBaseChangeRightTensorNatIso q₀).app _


/-- 概要：実商環上の還元のホモロジーを制限した対象と、raw残余商とのH0同型。
方針：実商射の全射性と係数制限のホモロジー比較で、前工程の具体的比較を商作用へ降下する。
規約：構成する各作用は元の自由 δ 源射を固定する。
使われ方：BS Rem 7.15（著者版 p.62）の元の A/(p,d) 上への比較。 -/
def powerRootPrismMonicSourceQuotientDerivedRestrictedH0Iso_of_unconditional (hf : f.Monic) :
    (ModuleCat.restrictScalars q₀).obj
      ((DerivedCategory.homologyFunctor (ModuleCat Q₀) 0).obj
        (PowerRootPrismMonicSourceQuotientDerived_of_unconditional W hW f).obj) ≅ MRes :=
  ((derivedRestrictScalarsHomologyIso q₀ 0).app
      (PowerRootPrismMonicSourceQuotientDerived_of_unconditional W hW f).obj).symm ≪≫
    (DerivedCategory.homologyFunctor (ModuleCat L₀) 0).mapIso
      (DerivedCategory.Minus.ι.mapIso
        (powerRootPrismMonicSourceQuotientDerivedRestrictionIso_of_unconditional W hW f)) ≪≫
    powerRootPrismMonicSourceCoefficientResidueHomologyZeroIso_of_unconditional
      W hW f hf

/-- 概要：無限根モニック入力について、実商環上の還元そのものの非零次数ホモロジーが消える。
方針：実商射の全射性と係数制限のホモロジー比較で、前工程の具体的比較を商作用へ降下する。
規約：構成する各作用は元の自由 δ 源射を固定する。
使われ方：BS Rem 7.15（著者版 p.62）の元の A/(p,d) 上への比較。 -/
theorem powerRootPrismMonicSourceQuotientDerived_homology_isZero_of_unconditional
    (hf : f.Monic)
    (i : ℤ) (hi : i ≠ 0) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat Q₀) i).obj
      (PowerRootPrismMonicSourceQuotientDerived_of_unconditional W hW f).obj) := by
  have hz := powerRootPrismMonicSourceCoefficientResidue_homology_isZero_of_unconditional
    W hW f hf i hi
  have hz' := hz.of_iso ((DerivedCategory.homologyFunctor (ModuleCat L₀) i).mapIso
    (DerivedCategory.Minus.ι.mapIso
        (powerRootPrismMonicSourceQuotientDerivedRestrictionIso_of_unconditional W hW f)))
  have hr := (derivedRestrictScalarsHomologyIso q₀ i).app
    (PowerRootPrismMonicSourceQuotientDerived_of_unconditional W hW f).obj
  have hs := hr.isZero_iff.mp hz'
  let : Subsingleton ((DerivedCategory.homologyFunctor (ModuleCat Q₀) i).obj
      (PowerRootPrismMonicSourceQuotientDerived_of_unconditional W hW f).obj) :=
    ModuleCat.subsingleton_of_isZero (R := L₀) hs
  exact ModuleCat.isZero_of_subsingleton _

set_option maxHeartbeats 800000 in
-- 無限根自由 δ 源の二つの制限スカラー作用と商の H⁰ 比較を同時に照合するため。
/-- 概要：実商環上でのH0同型。qの全射性により、L線形比較を実Q線形比較へ昇格する。
方針：実商射の全射性と係数制限のホモロジー比較で、前工程の具体的比較を商作用へ降下する。
規約：構成する各作用は元の自由 δ 源射を固定する。
使われ方：BS Rem 7.15（著者版 p.62）の元の A/(p,d) 上への比較。 -/
def powerRootPrismMonicSourceQuotientDerivedH0Iso_of_unconditional (hf : f.Monic) :
    letI := (powerRootPrismMonicSourceQuotientResidueMap_of_unconditional W hW f).toAlgebra
    letI : Module Q₀ Res₀ := Algebra.toModule
    ((DerivedCategory.homologyFunctor (ModuleCat Q₀) 0).obj
      (PowerRootPrismMonicSourceQuotientDerived_of_unconditional W hW f).obj) ≅
      ModuleCat.of Q₀ Res₀ := by
  letI := (powerRootPrismMonicSourceQuotientResidueMap_of_unconditional W hW f).toAlgebra
  letI : Module Q₀ Res₀ := Algebra.toModule
  let e := powerRootPrismMonicSourceQuotientDerivedRestrictedH0Iso_of_unconditional
    W hW f hf ≪≫
      (powerRootPrismMonicSourceQuotientResidueRestrictionIso_of_unconditional W hW f).symm
  refine
    { hom := { hom' :=
        { toFun := e.hom.hom
          map_add' := e.hom.hom.map_add
          map_smul' := ?_ } }
      inv := { hom' :=
        { toFun := e.inv.hom
          map_add' := e.inv.hom.map_add
          map_smul' := ?_ } }
      hom_inv_id := ?_
      inv_hom_id := ?_ }
  · intro s x
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective s
    have h := e.hom.hom.map_smul r x
    change e.hom.hom ((q₀ r) • x) = (q₀ r) • e.hom.hom x at h
    exact h
  · intro s x
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective s
    have h := e.inv.hom.map_smul r x
    change e.inv.hom ((q₀ r) • x) = (q₀ r) • e.inv.hom x at h
    exact h
  · apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact congrArg (fun f => f.hom x) e.hom_inv_id
  · apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact congrArg (fun f => f.hom x) e.inv_hom_id

local notation "X₀" => PowerRootPrismMonicSourceQuotientDerived_of_unconditional W hW f

/-- 概要：無限根モニック入力の実商還元は、標準t構造の非負部分に属する。
方針：実商射の全射性と係数制限のホモロジー比較で、前工程の具体的比較を商作用へ降下する。
規約：構成する各作用は元の自由 δ 源射を固定する。
使われ方：BS Rem 7.15（著者版 p.62）の元の A/(p,d) 上への比較。 -/
theorem powerRootPrismMonicSourceQuotientDerived_isGE_zero_of_unconditional
    (hf : f.Monic) :
    DerivedCategory.IsGE (X₀).obj 0 := by
  apply (DerivedCategory.isGE_iff _ _).mpr
  intro i hi
  exact powerRootPrismMonicSourceQuotientDerived_homology_isZero_of_unconditional
    W hW f hf i (by omega)

/-- 概要：同じ入力の下で標準t構造の非正部分にも属する。
方針：実商射の全射性と係数制限のホモロジー比較で、前工程の具体的比較を商作用へ降下する。
規約：構成する各作用は元の自由 δ 源射を固定する。
使われ方：BS Rem 7.15（著者版 p.62）の元の A/(p,d) 上への比較。 -/
theorem powerRootPrismMonicSourceQuotientDerived_isLE_zero_of_unconditional
    (hf : f.Monic) :
    DerivedCategory.IsLE (X₀).obj 0 := by
  apply (DerivedCategory.isLE_iff _ _).mpr
  intro i hi
  exact powerRootPrismMonicSourceQuotientDerived_homology_isZero_of_unconditional
    W hW f hf i (by omega)

/-- 概要：実Q上の還元対象は、作用を降下した既存raw残余商の次数零対象と同型。
方針：実商射の全射性と係数制限のホモロジー比較で、前工程の具体的比較を商作用へ降下する。
規約：構成する各作用は元の自由 δ 源射を固定する。
使われ方：BS Rem 7.15（著者版 p.62）の元の A/(p,d) 上への比較。 -/
def powerRootPrismMonicSourceQuotientDerivedSingleIso_of_unconditional (hf : f.Monic) :
    letI := (powerRootPrismMonicSourceQuotientResidueMap_of_unconditional W hW f).toAlgebra
    letI : Module Q₀ Res₀ := Algebra.toModule
    X₀ ≅ boundedAboveDerivedSingleFunctor.obj (ModuleCat.of Q₀ Res₀) := by
  letI := (powerRootPrismMonicSourceQuotientResidueMap_of_unconditional W hW f).toAlgebra
  letI : Module Q₀ Res₀ := Algebra.toModule
  have := powerRootPrismMonicSourceQuotientDerived_isGE_zero_of_unconditional W hW f hf
  have := powerRootPrismMonicSourceQuotientDerived_isLE_zero_of_unconditional W hW f hf
  exact ObjectProperty.isoMk _ (normalizedPureHomologyIso (X₀).obj 0) ≪≫
    boundedAboveDerivedSingleFunctor.mapIso
      (powerRootPrismMonicSourceQuotientDerivedH0Iso_of_unconditional W hW f hf)



end SerrePositivity.BhattScholze.Andre
