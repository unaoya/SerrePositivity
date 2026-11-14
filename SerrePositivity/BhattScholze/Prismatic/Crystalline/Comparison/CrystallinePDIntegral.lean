module

public import SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.CrystallinePDInclusion
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.CrystallinePDInclusion
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.CrystallineExtraModel
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Envelopes.CrystallinePDModel
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.CrystallineCompletedPushout
import all SerrePositivity.HomologicalAlgebra.DerivedCompletion.Principal.CompletionFunctor

/-!
# 高次座標を加える比較の整係数射

## 概要
分冪模型から結晶側模型への mod p の包含を整係数の自然変換から得る。

## 方針
未完備模型の写像を完備化の普遍性で延長し、mod p で分離した模型と照合する。

## 規約
完備化の単位を通して得られる延長を用いる。

## 使われ方
Bockstein との自然性。
-/

public noncomputable section

open CategoryTheory SerrePositivity.Cosimplicial SerrePositivity.DerivedCompletion
universe u

namespace SerrePositivity.BhattScholze.Prismatic

variable (p : ℕ) [Fact p.Prime] (r : ℕ)
local notation "K" => crystallineBase p
local notation "W" => withExtraCoords p (crystallineBase p) r
local notation "U" => Under.forget (CommRingCat.of (crystallineBase p))

private theorem pdDelta_complete (n : SimplexCategory) :
    IsModuleComplete ((pdDeltaRings.{u} p r).obj n) (p : (pdDeltaRings.{u} p r).obj n)
      (ModuleCat.of ((pdDeltaRings.{u} p r).obj n) ((pdDeltaRings.{u} p r).obj n)) :=
  classicalPDivision_isModuleComplete
    (completedFreeDeltaStructure (crystallineBasePrism.{u} p) (AffineIndex.{u} r n.len))
    (crystallinePDDifference.{u} p r n)

/-- 完備環への環射は主完備化を一意に経由する。 -/
private theorem principalCompletionRingCat_existsUnique (p : ℕ) {S T : CommRingCat.{u}}
    (f : S ⟶ T)
    (hT : IsModuleComplete T (p : T) (ModuleCat.of T T)) :
    ∃! g : principalCompletionRingCat p S ⟶ T, principalCompletionRingCatUnit p S ≫ g = f := by
  let := principalCompletionCommRing S (p : S)
  let := f.hom.toAlgebra
  have h : IsModuleComplete S (p : S) (ModuleCat.of S T) := by
    apply (isModuleComplete_algebraMap_iff S T (p : S) T).mp
    simpa only [map_natCast] using hT
  obtain ⟨g, hg, hu⟩ := principalCompletion_existsUnique_ringHom S (p : S) T f.hom h
  refine ⟨CommRingCat.ofHom g, CommRingCat.hom_ext hg, fun k hk => ?_⟩
  apply CommRingCat.hom_ext
  exact hu k.hom (congrArg CommRingCat.Hom.hom hk)

private theorem completedApp_exists (n : SimplexCategory) :
    ∃! g : (W ⋙ U).obj n ⟶ (pdDeltaRings.{u} p r).obj n,
      (extraCompletionUnit.{u} p r).app n ≫ g = (extraToTarget.{u} p r).app n :=
  principalCompletionRingCat_existsUnique p ((extraToTarget p r).app n) (pdDelta_complete p r n)

private def completedToTarget : W ⋙ U ⟶ pdDeltaRings.{u} p r where
  app n := (completedApp_exists p r n).choose
  naturality m n θ := by
    let j := extraCompletionUnit.{u} p r
    let f := extraToTarget.{u} p r
    let gM := (completedApp_exists.{u} p r m).choose
    let gN := (completedApp_exists.{u} p r n).choose
    have hM : j.app m ≫ gM = f.app m := (completedApp_exists p r m).choose_spec.1
    have hN : j.app n ≫ gN = f.app n := (completedApp_exists p r n).choose_spec.1
    have H := principalCompletionRingCat_existsUnique p
      ((crystallineExtraRaw (crystallineBase.{u} p) r ⋙ U).map θ ≫ f.app n)
      (pdDelta_complete p r n)
    let a := (crystallineExtraRaw (crystallineBase.{u} p) r ⋙ U).map θ
    let b := (W ⋙ U).map θ
    let c := (pdDeltaRings.{u} p r).map θ
    change b ≫ gN = gM ≫ c
    have h₁ : j.app m ≫ (b ≫ gN) = a ≫ f.app n := by
      calc
        _ = (j.app m ≫ b) ≫ gN := (Category.assoc _ _ _).symm
        _ = (a ≫ j.app n) ≫ gN := congrArg (fun k => k ≫ gN) (j.naturality θ).symm
        _ = a ≫ (j.app n ≫ gN) := Category.assoc _ _ _
        _ = _ := congrArg (a ≫ ·) hN
    have h₂ : j.app m ≫ (gM ≫ c) = a ≫ f.app n := by
      calc
        _ = (j.app m ≫ gM) ≫ c := (Category.assoc _ _ _).symm
        _ = f.app m ≫ c := congrArg (fun k => k ≫ c) hM
        _ = _ := (f.naturality θ).symm
    exact H.unique h₁ h₂

private theorem completedToTarget_spec :
    extraCompletionUnit.{u} p r ≫ completedToTarget.{u} p r = extraToTarget.{u} p r := by
  apply NatTrans.ext
  funext n
  exact (completedApp_exists p r n).choose_spec.1

private theorem rawToTarget_base (n : SimplexCategory) :
    ((crystallineExtraRaw (crystallineBase.{u} p) r).obj n).hom ≫
      (extraToTarget.{u} p r).app n = ((pdDeltaModel.{u} p r).obj n).hom := by
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro x
  change extraToTargetApp p r n (((crystallineExtraRaw (crystallineBase.{u} p) r).obj n).hom x) = _
  have h := rawCoordToExtra_C.{u} p r n x
  exact (congrArg (extraToTargetApp p r n) h.symm).trans
    (extraToTargetApp_coord.{u} p r n (MvPolynomial.C x))

private def completedToTargetUnder : W ⟶ pdDeltaModel.{u} p r where
  app n := Under.homMk ((completedToTarget p r).app n) (by
    change (((crystallineExtraRaw (crystallineBase.{u} p) r).obj n).hom ≫
      (extraCompletionUnit p r).app n) ≫ (completedToTarget p r).app n = _
    have H : (extraCompletionUnit p r).app n ≫ (completedToTarget p r).app n =
        (extraToTarget p r).app n := NatTrans.congr_app (completedToTarget_spec p r) n
    exact (Category.assoc _ _ _).trans
      ((congrArg (((crystallineExtraRaw (crystallineBase.{u} p) r).obj n).hom ≫ ·) H).trans
        (rawToTarget_base p r n)))
  naturality _ _ θ := Under.UnderMorphism.ext ((completedToTarget p r).naturality θ)

/-- 高次座標を除いた完備 pd 模型から結晶模型への整係数の射。 -/
def pdInclusion : pdModel.{u} p (crystallineBase.{u} p) r ⟶ pdDeltaModel.{u} p r :=
  insertPdFactor p (crystallineBase.{u} p) r ≫ completedToTargetUnder p r

omit [Fact p.Prime] in
private theorem modPrimeMap_comp {X Y Z : CosimplicialObject CommRingCat.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    modPrimeMap p (f ≫ g) = modPrimeMap p f ≫ modPrimeMap p g := by
  apply NatTrans.ext
  funext n
  exact (ringMap_comp (p := p) (f.app n) (g.app n)).symm

private theorem split_inv_eq_completed :
    (splitDeltaCoordinatesModP.{u} p r).inv = modPrimeMap p (completedToTarget.{u} p r) := by
  let j := extraCompletionUnit.{u} p r
  let g := completedToTarget.{u} p r
  let f := extraToTarget.{u} p r
  have hj (n : SimplexCategory) : IsIso (crystallineModPrimeRingMap p (j.app n)) :=
    crystallinePrincipalCompletionUnit_isIso_modPrime p _ (rawExtra_primeRegular p r n)
  let := iso_modPrime_of_components p j hj
  apply (cancel_epi (modPrimeMap p j)).mp
  have hg : modPrimeMap p j ≫ modPrimeMap p g = modPrimeMap p f :=
    (modPrimeMap_comp p j g).symm.trans
      (congrArg (modPrimeMap p) (completedToTarget_spec p r))
  rw [hg]
  change modPrimeMap p j ≫ ((asIso (modPrimeMap p j)).inv ≫ modPrimeMap p f) = _
  exact (asIso (modPrimeMap p j)).hom_inv_id_assoc _

/-- mod p の包含は整係数の比較射の還元なので、Bockstein の自然性を適用できる。 -/
theorem pdInclusionModP_eq_modPrime :
    pdInclusionModP.{u} p r =
      modPrimeMap p (Functor.whiskerRight (pdInclusion.{u} p r) U) := by
  change modPrimeMap p (Functor.whiskerRight (insertPdFactor p (crystallineBase.{u} p) r) U) ≫
    (splitDeltaCoordinatesModP p r).inv = _
  rw [split_inv_eq_completed, ← modPrimeMap_comp]
  rfl

end SerrePositivity.BhattScholze.Prismatic
