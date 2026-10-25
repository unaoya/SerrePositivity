module

public import SerrePositivity.BhattScholze.Andre.Unconditional.SourceUnitDenominator
public import SerrePositivity.BhattScholze.Delta.Division.DeltaDivisionSourceCoefficientTor
public import SerrePositivity.HomologicalAlgebra.DerivedTensorAugmentationIso

/-!
# 単元分母での元の二因子導来源の純性

## 概要
BS Rem 7.15（著者版 p.62）の実源の分母可逆部分では、高次 Tor は消える。

## 方針
実源射の逆射を使って右因子を自由な一階加群へ比較する。
Tor の対称性と元の標準 augmentation に沿って純性を得る。

## 規約
元の係数作用を保つ。分子の正則性・モニック性・係数環の p 正則性は不要。

## 使われ方
元の源の局所化比較後に、局所化側の負次数消滅を供給する。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.BhattScholze.Andre
open CategoryTheory CategoryTheory.Limits
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local instance] HasDerivedCategory.standard
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
local notation "L" => RelativeFreeDeltaRing (R := A) σ

/-- 概要：単元分母の実源射による係数加群は平坦。
方針：逆射を使い、同じ係数環の自由一階加群へ線形同型を作る。
規約：元の実源射によるスカラー作用を用いる。
使われ方：BS Rem 7.15（著者版 p.62）の局所化側の Tor 消滅。 -/
theorem unconditionalSourceUnit_scalarModule_flat
    (D : DeltaStructure p A) (d : A) (hd : IsUnit d) :
    Module.Flat L (baseChangeScalarModule (deltaDivisionSourceMap (σ := σ) D d)) := by
  let α := deltaDivisionSourceMap (σ := σ) D d
  let e := RingEquiv.ofBijective α
    (unconditionalDeltaDivisionSourceMap_bijective_of_isUnit D d hd)
  let eM : baseChangeScalarModule α ≃ₗ[L] L :=
    { e.symm.toAddEquiv with
      map_smul' := by
        intro r x
        change L at x
        change e.symm (α r * x) = r * e.symm x
        rw [map_mul]
        congr 1
        exact e.symm_apply_apply r }
  exact Module.Flat.of_linearEquiv eM

/-- 概要：単元分母の実二因子源の高次 Tor は零。
方針：右因子の平坦性と Tor の対称性を使う。
規約：分子族は任意でよい。
使われ方：BS Rem 7.15（著者版 p.62）の標準 augmentation の同型性。 -/
theorem unconditionalSourceUnit_tor_isZero
    (D : DeltaStructure p A) (d : A) (hd : IsUnit d) (a : σ → A)
    (n : ℕ) (hn : 0 < n) :
    IsZero (((Tor (ModuleCat L) n).obj
      (baseChangeScalarModule (deltaDivisionSourceEval D a))).obj
        (baseChangeScalarModule (deltaDivisionSourceMap D d))) := by
  let Mβ := baseChangeScalarModule (deltaDivisionSourceEval D a)
  let Mα := baseChangeScalarModule (deltaDivisionSourceMap (σ := σ) D d)
  have : Module.Flat L Mα := unconditionalSourceUnit_scalarModule_flat D d hd
  cases n with
  | zero => omega
  | succ n =>
    have : Subsingleton (TorModule L (n + 1) Mα Mβ) :=
      torModule_subsingleton_of_flat Mα Mβ n
    exact ModuleCat.isZero_iff_subsingleton.mpr
      (torComm (n + 1) Mβ Mα).injective.subsingleton

/-- 概要：単元分母では元の二因子導来源の標準 augmentation が同型。
方針：同じ実二因子の Tor 消滅を標準 augmentation の判定へ渡す。
規約：通常テンソルへの元の射について述べる。
使われ方：BS Rem 7.15（著者版 p.62）の局所化側の純性比較。 -/
theorem unconditionalSourceUnit_augmentation_isIso
    (D : DeltaStructure p A) (d : A) (hd : IsUnit d) (a : σ → A) :
    IsIso ((boundedAboveDerivedTensorModuleAugmentation
      (baseChangeScalarModule (deltaDivisionSourceEval D a))).app
        (baseChangeScalarModule (deltaDivisionSourceMap D d))) :=
  derivedTensorAugmentation_isIso_of_tor _ _
    (unconditionalSourceUnit_tor_isZero D d hd a)

/-- 概要：単元分母での元の二因子導来源は全非零次数でホモロジーが消える。
方針：元の標準 augmentation の同型で通常テンソルの single へ移す。
規約：完備化・ねじれ除去は行わない。
使われ方：BS Rem 7.15（著者版 p.62）の局所化側の消滅判定。 -/
theorem unconditionalSourceUnit_homology_isZero
    (D : DeltaStructure p A) (d : A) (hd : IsUnit d) (a : σ → A)
    (i : ℤ) (hi : i ≠ 0) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat L) i).obj
      (boundedAboveDerivedTensor.obj
        (boundedAboveDerivedSingleFunctor.obj
            (baseChangeScalarModule (deltaDivisionSourceEval D a)),
          boundedAboveDerivedSingleFunctor.obj
            (baseChangeScalarModule (deltaDivisionSourceMap D d)))).obj) := by
  let Mβ := baseChangeScalarModule (deltaDivisionSourceEval D a)
  let Mα := baseChangeScalarModule (deltaDivisionSourceMap (σ := σ) D d)
  have := unconditionalSourceUnit_augmentation_isIso D d hd a
  exact (derivedSingleHomology_isZero ((CategoryTheory.MonoidalCategory.tensorLeft Mβ).obj Mα)
    i hi).of_iso ((DerivedCategory.homologyFunctor (ModuleCat L) i).mapIso
      (asIso ((boundedAboveDerivedTensorModuleAugmentation Mβ).app Mα)))

/-- 概要：安定局所化した係数と元の分子像による実源の非零次ホモロジーは零。
方針：元の分母の単元性を局所化から供給して前の純性定理を使う。
規約：係数と分子の像は標準局所化射で指定する。
使われ方：BS Rem 7.15（著者版 p.62）の元の源の係数局所化後の比較先。 -/
theorem unconditionalSourceSaturatedLocalization_homology_isZero
    (D : DeltaStructure p A) (d : A) (a : σ → A)
    (B : Type u) [CommRing B] [Algebra A B]
    [IsLocalization (D.frobeniusDenominators (Submonoid.powers d)) B]
    (i : ℤ) (hi : i ≠ 0) :
    let E := D.localization (D.frobeniusDenominators (Submonoid.powers d)) B
      (D.frobeniusDenominators_stable (Submonoid.powers d))
    let α := deltaDivisionSourceMap (σ := σ) E (algebraMap A B d)
    let β := deltaDivisionSourceEval E (fun s => algebraMap A B (a s))
    IsZero ((DerivedCategory.homologyFunctor
      (ModuleCat (RelativeFreeDeltaRing (R := B) σ)) i).obj
      (boundedAboveDerivedTensor.obj
        (boundedAboveDerivedSingleFunctor.obj (baseChangeScalarModule β),
          boundedAboveDerivedSingleFunctor.obj (baseChangeScalarModule α))).obj) := by
  apply unconditionalSourceUnit_homology_isZero _ _ _ _ i hi
  exact IsLocalization.map_units B
    ⟨d, D.le_frobeniusDenominators (Submonoid.powers d) (Submonoid.mem_powers d)⟩

end SerrePositivity.BhattScholze.Andre
