module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.Comparison.CrystallineWittTransportedBridge
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.Comparison.CrystallineWittSmallCoefficients
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.Comparison.CrystallineWittTransportedBridge
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.AffineCechPointwiseCoefficients
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.Comparison.CrystallineWittSmallCoefficients
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.Comparison.CrystallineWittSmallFrame
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.Comparison.CrystallineSmallBridgeFrame
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.Comparison.CrystallineSmallBridgeComplex
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.Comparison.CrystallineSmallBridge
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.CrystallineBase
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.Comparison.CrystallineWittCoefficients
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Affine.HodgeTateAffineModel
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.Comparison.PDCompletedCoefficientComplex
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.Comparison.PDTermPointwiseNaturality
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.PDCompletedCech
import all SerrePositivity.HomologicalAlgebra.Cosimplicial.Algebra
import all SerrePositivity.HomologicalAlgebra.Cosimplicial.ModuleMap
import all SerrePositivity.HomologicalAlgebra.Cosimplicial.MapComplex
import all SerrePositivity.HomologicalAlgebra.DerivedCompletion.PointwiseBaseChange
import all Mathlib.AlgebraicTopology.AlternatingFaceMapComplex

/-!
# 移した Witt の橋と指定された環射の照合

## 概要
整係数の橋から移した射が、有限 affine 枠の既存の Witt の橋であることを示す。

## 方針
完備係数拡大の純テンソルの単位上で照合し、係数射の正方形と線形写像の一意性を使う。

## 規約
Witt の橋の環射は既存のものを使う。

## 使われ方
BS 著者版 Theorem 6.4、指定された結晶の橋の擬同型。
-/

public noncomputable section
open CategoryTheory AlgebraicTopology
open scoped TensorProduct Simplicial ChangeOfRings
open SerrePositivity.DerivedCompletion
universe u
namespace SerrePositivity.BhattScholze.Prismatic
set_option backward.isDefEq.respectTransparency false
variable (p : ℕ) [Fact p.Prime] (C : Type u) [CommRing C]
variable (hpC : Function.Injective (fun x : C => (p : C) * x))
variable (hlocalC : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : C))
variable [IsAdicComplete (Ideal.span {(p : C)}) C] (r n : ℕ)
local notation "W" => WittVector p C
local notation "Q" => wittCrystallinePrism hpC
local notation "hQ" => crystallineBounded p Q rfl
local notation "V" => affineEnvelopeTerm Q hQ r n
  (cutoff W (prismPolynomialCompletion Q (Fin r))) le_rfl
local notation "f" => crystallineWittBaseMap p C hpC
local notation "F" => pCompletedScalarExtensionFunctor p f

/-- 指定された Witt の橋の各項を、実際の交代余面複体の加群射として読む。 -/
def crystallineWittSmallBridgeTermMap :
    (crystallineWittAffineComplex p C hpC r).X n ⟶ (crystallineWittPDComplex p C r).X n := by
  let := (V).X.toHom.toRingHom.toAlgebra
  change ModuleCat.of W (V).X.B ⟶ ModuleCat.of W (pdTerm p W r n)
  let g := crystallineWittSmallBridgeAt p C hpC hlocalC r n V
  exact ModuleCat.ofHom {
    toFun := g
    map_add' := g.map_add
    map_smul' := fun b x => by
      change g ((V).X.toHom.toRingHom b * x) = algebraMap W (pdTerm p W r n) b * g x
      rw [map_mul, crystallineWittSmallBridgeAt_base]
  }

private theorem sourceIso_unit (b : W) (x : ((crystallineSmallBridgeAffineTerm.{u} p r n)).X.B) :
    letI := (f).toAlgebra
    letI := ((crystallineSmallBridgeAffineTerm.{u} p r n)).X.toHom.toRingHom.toAlgebra
    letI := (V).X.toHom.toRingHom.toAlgebra
    (crystallineWittAffineComplexIso p C hpC r).hom.f n
      (((moduleCompletionH0Unit W (p : W)).app
        ((ModuleCat.extendScalars (f)).obj (ModuleCat.of (crystallineBase.{u} p)
          ((crystallineSmallBridgeAffineTerm.{u} p r n)).X.B)))
          (b ⊗ₜ[(crystallineBase.{u} p),f] x)) =
      b • affineEnvelopeCoefficientMap (crystallineWittBaseHom p C hpC)
        (crystallineSmallBridgeAffineTerm.{u} p r n) V x := by
  let := (f).toAlgebra
  let := ((crystallineSmallBridgeAffineTerm.{u} p r n)).X.toHom.toRingHom.toAlgebra
  let := (V).X.toHom.toRingHom.toAlgebra
  exact component_unit (crystallineBasePrism.{u} p) Q (crystallineBaseBounded.{u} p) hQ rfl
    (crystallineWittBaseHom p C hpC) r n b x

private theorem targetIso_unit (b : W) (x : pdTerm p (crystallineBase.{u} p) r n) :
    letI := (f).toAlgebra
    (crystallineWittPDComplexIso p C hpC r).hom.f n
      (((moduleCompletionH0Unit W (p : W)).app
        ((ModuleCat.extendScalars (f)).obj (ModuleCat.of (crystallineBase.{u} p) (pdTerm p
          (crystallineBase.{u} p) r n))))
          (b ⊗ₜ[(crystallineBase.{u} p),f] x)) =
            b • crystallineWittSmallModelCoefficient p C hpC r n x := by
  let := (f).toAlgebra
  exact pdTermPointwiseCoefficientIso_unit_smul p (crystallineBase.{u} p) W r n b x

private theorem integralBridge_at (x : ((crystallineSmallBridgeAffineTerm.{u} p r n)).X.B) :
    crystallineSmallModelBridgeAt p r n x = (crystallineSmallBridgeCochainMap.{u} p r).f n x := by
  change (crystallineSmallBridgeFrameEquiv.{u} p r n).symm
    (crystallineSmallBridgeFrameEquiv.{u} p r n ((crystallineSmallBridge.{u} p r).app ⦋n⦌ x)) = _
  exact (crystallineSmallBridgeFrameEquiv.{u} p r n).symm_apply_apply _

/-- 移した橋の各項は、指定された Witt の環射そのものである。 -/
theorem crystallineWittTransportedBridge_f :
    (crystallineWittTransportedBridge p C hpC r).f n =
      crystallineWittSmallBridgeTermMap p C hpC hlocalC r n := by
  let := (f).toAlgebra
  let := ((crystallineSmallBridgeAffineTerm.{u} p r n)).X.toHom.toRingHom.toAlgebra
  let := (V).X.toHom.toRingHom.toAlgebra
  let eS := crystallineWittAffineComplexIso p C hpC r
  let eT := crystallineWittPDComplexIso p C hpC r
  apply (cancel_epi (eS.hom.f n)).mp
  have he : eS.hom.f n ≫ eS.inv.f n = 𝟙 _ := by
    rw [← HomologicalComplex.comp_f, eS.hom_inv_id]
    rfl
  change eS.hom.f n ≫ ((eS.inv.f n ≫
      (((F).mapHomologicalComplex _).map (crystallineSmallBridgeCochainMap.{u} p r)).f n) ≫
        eT.hom.f n) = eS.hom.f n ≫ crystallineWittSmallBridgeTermMap p C hpC hlocalC r n
  simp only [← Category.assoc, he, Category.id_comp]
  apply pCompletedScalarExtension_hom_ext p (crystallineBase.{u} p) W
    ((crystallineSmallBridgeAffineTerm.{u} p r n)).X.B
    (ModuleCat.of W (pdTerm p W r n)) (completedRing_isModuleComplete W p (A := pdRaw W r n))
  intro b x
  change eT.hom.f n
      ((F).map ((crystallineSmallBridgeCochainMap.{u} p r).f n) _) =
    crystallineWittSmallBridgeTermMap p C hpC hlocalC r n (eS.hom.f n _)
  have hu := pCompletedScalarExtension_map_unit_linear p (crystallineBase.{u} p) W
    ((crystallineSmallBridgeCochainMap.{u} p r).f n) b x
  refine (congrArg (eT.hom.f n) hu).trans ?_
  refine (targetIso_unit p C hpC r n b ((crystallineSmallBridgeCochainMap.{u} p r).f n x)).trans ?_
  have hs := sourceIso_unit p C hpC r n b x
  have hc := RingHom.congr_fun (crystallineWittSmallBridgeAt_coefficients p C hpC hlocalC r n V) x
  simp only [RingHom.comp_apply] at hc
  rw [integralBridge_at] at hc
  have heq := congrArg (b • ·) hc
  have hr := congrArg (crystallineWittSmallBridgeTermMap p C hpC hlocalC r n) hs
  exact heq.trans ((map_smul (crystallineWittSmallBridgeTermMap p C hpC hlocalC r n).hom b
    (affineEnvelopeCoefficientMap (crystallineWittBaseHom p C hpC)
      (crystallineSmallBridgeAffineTerm.{u} p r n) V x)).symm.trans hr.symm)

end SerrePositivity.BhattScholze.Prismatic
