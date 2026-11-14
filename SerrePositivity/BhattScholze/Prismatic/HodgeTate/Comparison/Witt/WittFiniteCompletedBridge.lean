module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.Comparison.CrystallineWittBridgeAgreement
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.WittFiniteBridgeCrystallineFactor
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.BaseChange.AffineEnvelopeDerivedBaseChange
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.Comparison.CrystallineWittTransportedBridge
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.Comparison.CrystallineWittBridgeAgreement
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.AffineCechPointwiseCoefficients
import all SerrePositivity.BhattScholze.Prismatic.CechAlexander.Envelopes.AffineEnvelopeConstruction
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Affine.HodgeTateAffineModel
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.WittCrystallinePrism
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.CrystallineBase
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.WittFiniteBridge
import all SerrePositivity.HomologicalAlgebra.Cosimplicial.MapComplex
import all SerrePositivity.HomologicalAlgebra.Cosimplicial.Algebra
import all SerrePositivity.HomologicalAlgebra.DerivedCompletion.PointwiseBaseChange

/-!
# 有限結晶の橋の完備係数変更後の擬同型

## 概要
一般の有界 prism から Witt 結晶基底への係数変更後、指定された有限結晶の橋は擬同型。

## 方針
有限 affine 模型の完備係数比較を、Witt 基底上の小さい橋の擬同型と合成する。
純テンソルの単位上で既存の有限環射との一致を固定する。

## 規約
各項の完備係数拡大による古典的複体を使う。各項の導来計算は
`affineEnvelopeTermCompletedBaseChangeToTargetIso` による。

## 使われ方
BS 著者版 Theorem 6.4、結晶の橋 β の有限枠による照合。
-/

public noncomputable section
open CategoryTheory AlgebraicTopology
open scoped TensorProduct Simplicial ChangeOfRings
open SerrePositivity.DerivedCompletion
universe u
namespace SerrePositivity.BhattScholze.Prismatic
set_option backward.isDefEq.respectTransparency false
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] (P : OrientedPrism p A)
variable (hpA : Function.Injective (fun x : A => (p : A) * x))
variable (hpC : Function.Injective (fun x : A ⧸ P.ideal => (p : A ⧸ P.ideal) * x))
variable [hC : IsAdicComplete (Ideal.span {(p : A ⧸ P.ideal)}) (A ⧸ P.ideal)]
variable (hP : IsBoundedPrism P) (T : Poly (A ⧸ P.ideal))
variable (hlocalC : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A ⧸ P.ideal)) (n : ℕ)
local notation "C" => A ⧸ P.ideal
local notation "W" => WittVector p C
local notation "Q" => wittCrystallinePrism hpC
local notation "hQ" => crystallineBounded p Q rfl
local notation "ψ" => psiRing P hpA
local notation "F" => pCompletedScalarExtensionFunctor p ψ

/-- 有限 affine 交代余面複体の各項を ψ で完備係数拡大した複体。 -/
@[expose] def wittFiniteCompletedSource : CochainComplex (ModuleCat.{u} W) ℕ :=
  ((F).mapHomologicalComplex _).obj
    ((alternatingCofaceMapComplex (ModuleCat A)).obj
      (SerrePositivity.Cosimplicial.toModules A (htRings P hP T.n) (htBase P hP T.n)))

private def sourceIso :
    wittFiniteCompletedSource P hpA hP T ≅ crystallineWittAffineComplex p C hpC T.n :=
  (SerrePositivity.Cosimplicial.alternatingCofaceMapComplexCompMapHomologicalComplexIso
      (F)).app (SerrePositivity.Cosimplicial.toModules A (htRings P hP T.n) (htBase P hP T.n)) ≪≫
    (alternatingCofaceMapComplex (ModuleCat W)).mapIso
      (affineCechPointwiseCoefficientIso P Q hP hQ rfl (psiPrism P hpA hpC) T.n)

/-- ψ による完備係数変更後の有限結晶の橋。 -/
def wittFiniteCompletedBridge :
    wittFiniteCompletedSource P hpA hP T ⟶ crystallineWittPDComplex p C T.n :=
  (sourceIso P hpA hpC hP T).hom ≫ crystallineWittTransportedBridge p C hpC T.n

/-- 完備係数変更後の有限結晶の橋は擬同型。 -/
theorem wittFiniteCompletedBridge_quasiIso :
    QuasiIso (wittFiniteCompletedBridge P hpA hpC hP T) := by
  have := crystallineWittTransportedBridge_quasiIso p C hpC T.n
  dsimp only [wittFiniteCompletedBridge]
  infer_instance

local notation "X" => affineEnvelopeTerm P hP T.n n
  (cutoff A (prismPolynomialCompletion P (Fin T.n))) le_rfl
local notation "V" => affineEnvelopeTerm Q hQ T.n n
  (cutoff W (prismPolynomialCompletion Q (Fin T.n))) le_rfl

/-- 既存の有限橋の環射を、実際の複体の項の間の関数として読む。 -/
def wittFiniteBridgeTermFunction :
    (SerrePositivity.Cosimplicial.toModules A (htRings P hP T.n) (htBase P hP T.n)).obj ⦋n⦌ →
      (crystallineWittPDComplex p C T.n).X n :=
  WittFiniteBridge.finiteBridgeAt P hpA hpC hlocalC hC T n X

set_option maxRecDepth 1500 in
/-- 完備係数拡大の純テンソルの単位上で、比較は指定された有限橋を延長する。 -/
theorem wittFiniteCompletedBridge_unit (b : W)
    (x : (SerrePositivity.Cosimplicial.toModules A (htRings P hP T.n) (htBase P hP T.n)).obj ⦋n⦌) :
    (wittFiniteCompletedBridge P hpA hpC hP T).f n
      (((moduleCompletionH0Unit W (p : W)).app
        ((ModuleCat.extendScalars (ψ)).obj
          ((SerrePositivity.Cosimplicial.toModules A
            (htRings P hP T.n) (htBase P hP T.n)).obj ⦋n⦌)))
            (b ⊗ₜ[A,ψ] x)) = b • wittFiniteBridgeTermFunction P hpA hpC hP T hlocalC n x := by
  let := (ψ).toAlgebra
  let := (X).X.toHom.toRingHom.toAlgebra
  let := (V).X.toHom.toRingHom.toAlgebra
  have hs := component_unit P Q hP hQ rfl (psiPrism P hpA hpC) T.n n b x
  change (crystallineWittTransportedBridge p C hpC T.n).f n
    ((sourceIso P hpA hpC hP T).hom.f n _) = _
  refine (congrArg ((crystallineWittTransportedBridge p C hpC T.n).f n) hs).trans ?_
  refine ((crystallineWittTransportedBridge p C hpC T.n).f n).hom.map_smul b _ |>.trans ?_
  apply congrArg (b • ·)
  have he := ConcreteCategory.congr_hom
    (crystallineWittTransportedBridge_f p C hpC hlocalC T.n n)
      (affineEnvelopeCoefficientMap (psiPrism P hpA hpC) X V x)
  have hc := RingHom.congr_fun
    (wittFiniteBridgeAt_eq_crystalline_comp P hpA hpC hlocalC T n X V) x
  exact he.trans hc.symm

end SerrePositivity.BhattScholze.Prismatic
