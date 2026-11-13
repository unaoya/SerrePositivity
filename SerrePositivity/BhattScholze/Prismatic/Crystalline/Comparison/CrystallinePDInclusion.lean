module

public import SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.CrystallinePDTensorPresentation
public import SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.CrystallineRawPDSplit
public import SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.CrystallinePrincipalResidue
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.CrystallineExtraModel
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.CrystallinePDTensorPresentation
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.CrystallineRawPDSplit
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.CrystallinePDRawComparison
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.CrystallineRawPDFactor
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.CrystallineExtraPolynomial
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.CrystallineCechResidue
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Envelopes.CrystallinePDModel
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.PDPolynomialCech
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.CrystallineCompletedPushout
import all SerrePositivity.HomologicalAlgebra.DerivedCompletion.Principal.CompletionFunctor

/-!
# 余分な δ 座標の mod p 比較

## 概要
高次 δ 座標の Čech 因子を加える包含は mod p のコホモロジー同型を誘導する。

## 方針
未完備模型の分離と完備化の剰余を比較し、切断付き Čech 因子を収縮する。

## 規約
余分な座標を除いた pd 模型の第 0 行はそのまま保つ。

## 使われ方
多項式の Hodge–Tate 比較。
-/

public noncomputable section

open CategoryTheory CategoryTheory.Limits SerrePositivity.Cosimplicial SerrePositivity.DerivedCompletion
open scoped TensorProduct

universe u

namespace SerrePositivity.BhattScholze.Prismatic

variable (p : ℕ) [Fact p.Prime] (r : ℕ)

local notation "K" => crystallineBase p
local notation "Raw" => crystallineExtraRaw (crystallineBase p) r
local notation "V" => Under.forget (CommRingCat.of (crystallineBase p))

/-- 高次 δ 座標を除いた完備 pd 模型の台環。 -/
abbrev pdRings := pdModel p (crystallineBase.{u} p) r ⋙
  Under.forget (CommRingCat.of (crystallineBase.{u} p))

private def rawSplitTerm (m : SimplexCategory) :
    let B := RelativeFreeDeltaRing (R := crystallineBase.{u} p) (AffineIndex.{u} r m.len)
    let D := relativeFreeDeltaStructure (AffineIndex.{u} r m.len) (crystallineBasePrism.{u} p).deltaStructure
    DeltaAdjoinDivision D (p : B) (crystallineRawPDDifference.{u} p r m.len) ≃+*
      ((crystallineExtraRaw (crystallineBase.{u} p) r).obj m).right :=
  (crystallineRawPDSplit.{u} p r m.len).trans
    (crystallineExtraTermIso (crystallineBase.{u} p) r m).commRingCatIsoToRingEquiv

private def rawCoordToExtra (m : SimplexCategory) :
    RelativeFreeDeltaRing (R := crystallineBase.{u} p) (AffineIndex.{u} r m.len) →+*
      ((crystallineExtraRaw (crystallineBase.{u} p) r).obj m).right :=
  (rawSplitTerm.{u} p r m).toRingHom.comp (rawJ.{u} p r m.len)

private theorem rawCoordToExtra_C (m : SimplexCategory) (x : crystallineBase.{u} p) :
    rawCoordToExtra.{u} p r m (MvPolynomial.C x) = ((Raw).obj m).hom x := by
  let e := crystallineExtraTermIso (crystallineBase.{u} p) r m
  change e.hom (crystallineRawPDSplit.{u} p r m.len (rawJ.{u} p r m.len (MvPolynomial.C x))) = _
  rw [rawPDSplit_C]

  refine (extraTermIso_left (crystallineBase.{u} p) r m
    (MvPolynomial.C x ⊗ₜ[crystallineBase.{u} p] 1)).trans ?_
  exact ConcreteCategory.congr_hom
    (coprod.inl : (pdRawModel (crystallineBase.{u} p) r).obj m ⟶ (Raw).obj m).w x

private theorem rawCoordToExtra_zero (m : SimplexCategory) (j : Fin r) (i : Fin (m.len + 1)) :
    rawCoordToExtra.{u} p r m (MvPolynomial.X (⟨(j,i)⟩,0)) =
      extraLeft (crystallineBase.{u} p) r m (copy (crystallineBase.{u} p) r m j i) := by
  let e := crystallineExtraTermIso (crystallineBase.{u} p) r m
  change e.hom (crystallineRawPDSplit.{u} p r m.len (rawJ.{u} p r m.len (MvPolynomial.X (⟨(j,i)⟩,0)))) = _
  rw [rawPDSplit_copy]
  exact extraTermIso_left (crystallineBase.{u} p) r m (copy (crystallineBase.{u} p) r m j i)

private theorem rawCoordToExtra_succ (m : SimplexCategory) (j : Fin r) (i : Fin (m.len + 1)) (a : ℕ) :
    rawCoordToExtra.{u} p r m (MvPolynomial.X (⟨(j,i)⟩,a + 1)) =
      (extraRight (crystallineBase.{u} p) r m).right (MvPolynomial.X ((j,a),i)) := by
  let e := crystallineExtraTermIso (crystallineBase.{u} p) r m
  change e.hom (crystallineRawPDSplit.{u} p r m.len (rawJ.{u} p r m.len (MvPolynomial.X (⟨(j,i)⟩,a + 1)))) = _
  rw [rawPDSplit_extra]
  exact extraTermIso_right (crystallineBase.{u} p) r m (MvPolynomial.X ((j,a),i))

private theorem rawCoordToExtra_nat {m n : SimplexCategory} (θ : m ⟶ n) :
    (((Raw).map θ).right.hom).comp (rawCoordToExtra.{u} p r m) =
      (rawCoordToExtra.{u} p r n).comp (rawRename.{u} p r θ) := by
  apply MvPolynomial.ringHom_ext'
  · apply RingHom.ext
    intro a
    change ((Raw).map θ).right (rawCoordToExtra p r m (MvPolynomial.C a)) =
      rawCoordToExtra p r n (rawRename p r θ (MvPolynomial.C a))
    rw [show rawRename.{u} p r θ (MvPolynomial.C a) = MvPolynomial.C a from MvPolynomial.rename_C _ _,
      rawCoordToExtra_C, rawCoordToExtra_C]
    exact ConcreteCategory.congr_hom ((Raw).map θ).w a
  · rintro ⟨⟨⟨j,i⟩⟩,a⟩
    have hX : rawRename.{u} p r θ (MvPolynomial.X (⟨(j,i)⟩,a)) =
        MvPolynomial.X (⟨(j,θ.toOrderHom i)⟩,a) := MvPolynomial.rename_X _ _
    change ((Raw).map θ).right (rawCoordToExtra p r m (MvPolynomial.X (⟨(j,i)⟩,a))) =
      rawCoordToExtra p r n (rawRename p r θ (MvPolynomial.X (⟨(j,i)⟩,a)))
    rw [hX]
    cases a with
    | zero =>
        rw [rawCoordToExtra_zero, rawCoordToExtra_zero]
        exact (ConcreteCategory.congr_hom (extraLeft_nat (crystallineBase.{u} p) r θ)
          (copy (crystallineBase.{u} p) r m j i)).trans
            (congrArg (extraLeft (crystallineBase.{u} p) r n) (pdRawMap_copy (crystallineBase.{u} p) r θ j i))
    | succ a =>
        rw [rawCoordToExtra_succ, rawCoordToExtra_succ]
        exact (ConcreteCategory.congr_hom
          (congrArg Under.Hom.right (extraRight_nat (crystallineBase.{u} p) r θ))
          (MvPolynomial.X ((j,a),i))).trans
            (congrArg (extraRight (crystallineBase.{u} p) r n).right (MvPolynomial.rename_X _ _))

private def extraToTargetApp (m : SimplexCategory) :
    ((crystallineExtraRaw (crystallineBase.{u} p) r).obj m).right →+*
      (pdDeltaRings.{u} p r).obj m :=
  (crystallinePDRawToTarget.{u} p r m).comp (rawSplitTerm.{u} p r m).symm.toRingHom

set_option maxRecDepth 4096 in
-- 未完備モデルの係数環と完備結晶模型の係数射を照合する。
private theorem extraToTargetApp_coord (m : SimplexCategory)
    (x : RelativeFreeDeltaRing (R := crystallineBase.{u} p) (AffineIndex.{u} r m.len)) :
    extraToTargetApp.{u} p r m (rawCoordToExtra.{u} p r m x) =
      pdDeltaUnit.{u} p r m (crystallineCompletedFreeDeltaUnit p (AffineIndex.{u} r m.len) x) := by
  exact (congrArg (crystallinePDRawToTarget.{u} p r m)
    ((rawSplitTerm.{u} p r m).symm_apply_apply (rawJ.{u} p r m.len x))).trans
      (crystallinePDRawToTarget_comp.{u} p r m x)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1200000 in
-- 未完備モデルの自然性を自由 δ 座標で確かめる。
private def extraToTarget : Raw ⋙ V ⟶ pdDeltaRings.{u} p r where
  app m := CommRingCat.ofHom (extraToTargetApp p r m)
  naturality m n θ := by
    apply CommRingCat.hom_ext
    let E := rawSplitTerm.{u} p r m
    let f := (extraToTargetApp.{u} p r n).comp (((Raw).map θ).right.hom)
    let g := ((pdDeltaRings.{u} p r).map θ).hom.comp (extraToTargetApp p r m)
    change f = g
    have H : f.comp E.toRingHom = g.comp E.toRingHom := by
      apply rawPDDivision_ringHom_ext p r m.len
      · intro a ha
        let β := completedFreeDeltaBase (crystallineBasePrism.{u} p) (AffineIndex.{u} r n.len)
        let j : crystallineBase.{u} p →+* (pdDeltaRings.{u} p r).obj n :=
          (pdDeltaUnit.{u} p r n).comp β
        simpa only [map_natCast] using (crystallineBase_primeLocal.{u} p a ha).map j
      · exact classicalPDivision_p_mul_injective
          (completedFreeDeltaStructure (crystallineBasePrism.{u} p) (AffineIndex.{u} r n.len))
          (crystallinePDDifference.{u} p r n)
      · intro x
        change extraToTargetApp p r n (((Raw).map θ).right (rawCoordToExtra p r m x)) =
          (pdDeltaRings p r).map θ (extraToTargetApp p r m (rawCoordToExtra p r m x))
        have h := DFunLike.congr_fun (rawCoordToExtra_nat p r θ) x
        change ((Raw).map θ).right (rawCoordToExtra p r m x) =
          rawCoordToExtra p r n (rawRename p r θ x) at h
        let uM := crystallineCompletedFreeDeltaUnit p (AffineIndex.{u} r m.len)
        let uN := crystallineCompletedFreeDeltaUnit p (AffineIndex.{u} r n.len)
        let tM : completedFreeDelta (crystallineBasePrism.{u} p) (AffineIndex.{u} r m.len) →+*
            (pdDeltaRings.{u} p r).obj m := pdDeltaUnit p r m
        let tN : completedFreeDelta (crystallineBasePrism.{u} p) (AffineIndex.{u} r n.len) →+*
            (pdDeltaRings.{u} p r).obj n := pdDeltaUnit p r n
        have h₁ : (pdDeltaRings p r).map θ (tM (uM x)) =
            tN (crystallineCechSourceMap p r θ (uM x)) :=
          DFunLike.congr_fun (pdDeltaMap_spec p r θ).2 (uM x)
        have h₂ := DFunLike.congr_fun (sourceMap_comp_unit p r θ) x
        calc
          _ = extraToTargetApp p r n (rawCoordToExtra p r n (rawRename p r θ x)) :=
            congrArg (extraToTargetApp p r n) h
          _ = tN (uN (rawRename p r θ x)) :=
            extraToTargetApp_coord p r n (rawRename p r θ x)
          _ = tN (crystallineCechSourceMap p r θ (uM x)) :=
            congrArg tN h₂.symm
          _ = (pdDeltaRings p r).map θ (tM (uM x)) := h₁.symm
          _ = _ := congrArg ((pdDeltaRings p r).map θ) (extraToTargetApp_coord p r m x).symm
    apply RingHom.ext
    intro x
    obtain ⟨z, rfl⟩ := E.surjective x
    exact DFunLike.congr_fun H z

private theorem extraToTarget_isIso_modPrime (m : SimplexCategory) :
    IsIso (crystallineModPrimeRingMap p ((extraToTarget.{u} p r).app m)) := by
  let e := (rawSplitTerm.{u} p r m).symm.toCommRingCatIso
  let f := CommRingCat.ofHom (crystallinePDRawToTarget.{u} p r m)
  change IsIso (crystallineModPrimeRingMap p (e.hom ≫ f))
  rw [← ringMap_comp]
  have he : IsIso (crystallineModPrimeRingMap p e.hom) :=
    ((crystallineReducePrime p).mapIso e).isIso_hom
  have hf : IsIso (crystallineModPrimeRingMap p f) :=
    crystallinePDRawToTarget_isIso_modPrime p r m
  exact CategoryTheory.IsIso.comp_isIso

private def extraCompletionUnit :
    Raw ⋙ V ⟶ withExtraCoords p (crystallineBase.{u} p) r ⋙ V where
  app n := principalCompletionRingCatUnit p ((Raw).obj n).right
  naturality _ _ θ := (ringCatMap_comp_unit p ((Raw).map θ).right).symm

omit [Fact p.Prime] in
private theorem iso_modPrime_of_components {X Y : CosimplicialObject CommRingCat.{u}}
    (f : X ⟶ Y) (h : ∀ n, IsIso (crystallineModPrimeRingMap p (f.app n))) :
    IsIso (modPrimeMap p f) := by
  let h' (n : SimplexCategory) : IsIso ((modPrimeMap p f).app n) := h n
  exact NatIso.isIso_of_isIso_app _

private theorem rawExtra_primeRegular (n : SimplexCategory) :
    let X := ((crystallineExtraRaw (crystallineBase.{u} p) r).obj n).right
    IsSMulRegular X (p : X) := by
  dsimp only
  let E := rawSplitTerm.{u} p r n
  have h := crystallineRawPDDivision_primeRegular.{u} p r n.len
  intro x y hxy
  apply E.symm.injective
  apply h
  change _ * E.symm x = _ * E.symm y
  change (p : ((Raw).obj n).right) * x = (p : ((Raw).obj n).right) * y at hxy
  simpa only [map_mul, map_natCast] using congrArg E.symm hxy

private def splitOfNaturalMap (f : Raw ⋙ V ⟶ pdDeltaRings.{u} p r)
    (hf : ∀ n, IsIso (crystallineModPrimeRingMap p (f.app n))) :
    modPrimeCosimplicial p (pdDeltaRings.{u} p r) ≅
      modPrimeCosimplicial p (withExtraCoords p (crystallineBase.{u} p) r ⋙ V) := by
  let j := extraCompletionUnit.{u} p r
  have hj (n : SimplexCategory) : IsIso (crystallineModPrimeRingMap p (j.app n)) :=
    crystallinePrincipalCompletionUnit_isIso_modPrime p _ (rawExtra_primeRegular p r n)
  letI := iso_modPrime_of_components p f hf
  letI := iso_modPrime_of_components p j hj
  exact (asIso (modPrimeMap p f)).symm ≪≫ asIso (modPrimeMap p j)

private def inclusionOfSplit (e : modPrimeCosimplicial p (pdDeltaRings.{u} p r) ≅
      modPrimeCosimplicial p (withExtraCoords p (crystallineBase.{u} p) r ⋙ V)) :
    modPrimeCosimplicial p (pdRings.{u} p r) ⟶ modPrimeCosimplicial p (pdDeltaRings.{u} p r) :=
  modPrimeMap p (Functor.whiskerRight (insertPdFactor p (crystallineBase.{u} p) r) V) ≫ e.inv

private theorem inclusionOfSplit_isCohomologyIso
    (e : modPrimeCosimplicial p (pdDeltaRings.{u} p r) ≅
      modPrimeCosimplicial p (withExtraCoords p (crystallineBase.{u} p) r ⋙ V)) :
    IsCohomologyIso (inclusionOfSplit p r e) := by
  let f := Functor.whiskerRight (insertPdFactor p (crystallineBase.{u} p) r) V
  have h : IsCohomologyIso (modPrimeMap p f) :=
    insertPdFactorModP_isCohomologyIso (crystallineBase.{u} p) r p
  intro n
  let U := forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat
  let F := (Functor.whiskeringRight SimplexCategory CommRingCat AddCommGrpCat).obj U ⋙
    AlgebraicTopology.alternatingCofaceMapComplex AddCommGrpCat ⋙
    HomologicalComplex.homologyFunctor AddCommGrpCat (ComplexShape.up ℕ) n
  change Function.Bijective (F.map (modPrimeMap p f ≫ e.inv)).hom
  rw [F.map_comp]
  exact (isCohomologyIso_of_isIso e.inv n).comp (h n)

/-- 結晶模型の mod p を pd 模型と高次座標の Čech 因子に分離する。 -/
def splitDeltaCoordinatesModP :
    modPrimeCosimplicial p (pdDeltaRings.{u} p r) ≅
      modPrimeCosimplicial p (withExtraCoords p (crystallineBase.{u} p) r ⋙ V) :=
  splitOfNaturalMap p r (extraToTarget.{u} p r) (extraToTarget_isIso_modPrime p r)

/-- 高次座標のない pd 模型から結晶模型への mod p の包含。 -/
def pdInclusionModP :
    modPrimeCosimplicial p (pdRings.{u} p r) ⟶ modPrimeCosimplicial p (pdDeltaRings.{u} p r) :=
  inclusionOfSplit p r (splitDeltaCoordinatesModP.{u} p r)

/-- 余分な高次 δ 座標を加えても mod p のコホモロジーは変わらない。 -/
theorem pdInclusionModP_isCohomologyIso : IsCohomologyIso (pdInclusionModP.{u} p r) :=
  inclusionOfSplit_isCohomologyIso p r (splitDeltaCoordinatesModP.{u} p r)

end SerrePositivity.BhattScholze.Prismatic
