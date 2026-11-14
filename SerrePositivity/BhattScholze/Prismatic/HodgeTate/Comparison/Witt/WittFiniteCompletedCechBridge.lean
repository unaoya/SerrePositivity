module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.CompletedCechCoefficientMap
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.WittFiniteCompletedBridge
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.WittFiniteBridgeNaturality
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.CompletedCechCoefficientMap
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.WittFiniteCompletedBridge
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.WittFiniteBridgeNaturality
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.WittFiniteBridge
import all SerrePositivity.BhattScholze.Prismatic.CechAlexander.Envelopes.AffineEnvelopeConstruction
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Affine.HodgeTateAffineModel
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.Comparison.CrystallineWittTransportedBridge
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.PDCompletedCech
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.PDDeRham.PDDeRhamCech
import all SerrePositivity.HomologicalAlgebra.Cosimplicial.MapComplex
import all SerrePositivity.HomologicalAlgebra.Cosimplicial.Algebra
import all SerrePositivity.HomologicalAlgebra.DerivedCompletion.PointwiseBaseChange
import all Mathlib.AlgebraicTopology.AlternatingFaceMapComplex

/-!
# 枠の台加群関手で読んだ有限橋の完備比較

## 概要
有限結晶の橋の擬同型を、大きい枠との正方形に使う標準の完備 Čech 係数射として読む。

## 方針
両者を純テンソルの単位上で指定された有限環射と照合し、完備な標的への一意性を使う。

## 規約
有限 affine 各項の導来底変換の計算には既存の完全平坦性と有界性の比較を使う。

## 使われ方
BS 著者版 Theorem 6.4、有限・大きい枠の比較の正方形。
-/

public noncomputable section
open CategoryTheory AlgebraicTopology
open scoped TensorProduct ChangeOfRings Simplicial
open SerrePositivity.DerivedCompletion
universe u
namespace SerrePositivity.BhattScholze.Prismatic
set_option backward.isDefEq.respectTransparency false
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] (P : OrientedPrism p A)
variable (hpA : Function.Injective (fun x : A => (p : A) * x))
variable (hpC : Function.Injective (fun x : A ⧸ P.ideal => (p : A ⧸ P.ideal) * x))
variable (hlocal : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A ⧸ P.ideal))
variable [hC : IsAdicComplete (Ideal.span {(p : A ⧸ P.ideal)}) (A ⧸ P.ideal)]
variable (hP : IsBoundedPrism P) (T : Poly (A ⧸ P.ideal))
local notation "C" => A ⧸ P.ideal
local notation "W" => WittVector p C
local notation "D" => polyCosimplicialAlgebra P hP T.n
local notation "E" => pdModel p W T.n
local notation "U" => fun n => affineEnvelopeTerm P hP T.n n (polyCutoff P T.n) le_rfl
local notation "ψ" => psiRing P hpA

omit hC in
private theorem finiteTargetComplete (n : SimplexCategory) :
    IsModuleComplete W (p : W) ((E ⋙ PDCechNerve.algebraModule W).obj n) := by
  change IsModuleComplete W (p : W) (ModuleCat.of W (pdTerm p W T.n n.len))
  exact completedRing_isModuleComplete W p (A := pdRaw W T.n n.len)

/-- 有限橋を、枠の標準の完備係数射として読んだ余鎖写像。 -/
def wittFiniteCompletedCechBridge :
    ((pCompletedScalarExtensionFunctor p ψ).mapHomologicalComplex _).obj
      ((alternatingCofaceMapComplex (ModuleCat.{u} A)).obj (D ⋙ PDCechNerve.algebraModule A)) ⟶
    (alternatingCofaceMapComplex (ModuleCat.{u} W)).obj (E ⋙ PDCechNerve.algebraModule W) := by
  let : Algebra A W := (ψ).toAlgebra
  exact completedUnderCechCoefficientCochainMap p A W D E
    (WittFiniteBridge.finiteBridge P hpA hpC hlocal hC T U)
    (finiteTargetComplete P T)

set_option maxRecDepth 1500 in
/-- 枠の標準の完備係数射として読んだ、指定された有限橋は擬同型。 -/
theorem wittFiniteCompletedCechBridge_quasiIso :
    QuasiIso (wittFiniteCompletedCechBridge P hpA hpC hlocal hP T) := by
  let : Algebra A W := (ψ).toAlgebra
  have he : wittFiniteCompletedCechBridge P hpA hpC hlocal hP T =
      wittFiniteCompletedBridge P hpA hpC hP T := by
    apply HomologicalComplex.Hom.ext
    funext n
    let X := (U) n
    let : Algebra A X.X.B := X.X.toHom.toRingHom.toAlgebra
    apply pCompletedScalarExtension_hom_ext p A W X.X.B
      (ModuleCat.of W (pdTerm p W T.n n))
      (completedRing_isModuleComplete W p (A := pdRaw W T.n n))
    intro b x
    have hl := completedUnderCechCoefficientMap_unit p A W D E
      (WittFiniteBridge.finiteBridge P hpA hpC hlocal hC T U)
      (finiteTargetComplete P T) ⦋n⦌ b x
    have hr := wittFiniteCompletedBridge_unit P hpA hpC hP T hlocal n b x
    exact hl.trans hr.symm
  rw [he]
  exact wittFiniteCompletedBridge_quasiIso P hpA hpC hP T

end SerrePositivity.BhattScholze.Prismatic
