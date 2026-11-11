module

public import SerrePositivity.BhattScholze.Prismatic.WittFiniteCompletedCechBridge
public import SerrePositivity.BhattScholze.Prismatic.CechFrameAdditiveQuasiIso
public import SerrePositivity.BhattScholze.Prismatic.WittFiniteBridgeSquare
import all Mathlib.Algebra.Category.CommAlgCat.Basic
import all Mathlib.Algebra.Category.ModuleCat.Basic
import all SerrePositivity.BhattScholze.Prismatic.PDCechNerve
import all SerrePositivity.BhattScholze.Prismatic.CompletedCechCoefficientMap
import all SerrePositivity.BhattScholze.Prismatic.WittFiniteCompletedCechBridge
import all SerrePositivity.BhattScholze.Prismatic.WittFiniteBridgeNaturality
import all SerrePositivity.BhattScholze.Prismatic.WittFiniteBridgeSquare
import all SerrePositivity.BhattScholze.Prismatic.WittSmallFrame
import all SerrePositivity.BhattScholze.Prismatic.WittToSmallFrame
import all SerrePositivity.BhattScholze.Prismatic.WittBigBridge
import all SerrePositivity.BhattScholze.Prismatic.WittBigCrystalline
import all SerrePositivity.BhattScholze.Prismatic.BigPDModel
import all SerrePositivity.BhattScholze.Prismatic.BigCechAlexander
import all SerrePositivity.BhattScholze.Prismatic.BigCechFrameComparison
import all SerrePositivity.BhattScholze.Prismatic.BigCechFrameLift
import all SerrePositivity.BhattScholze.Prismatic.AffineEnvelopeConstruction
import all SerrePositivity.BhattScholze.Prismatic.PDCompletedCech

/-!
# 大きい結晶の橋の完備係数変更後の擬同型

## 概要
指定された大きい結晶の橋 β は、ψ による各項の完備係数変更後に擬同型となる。

## 方針
有限・大きい枠の厳密な正方形を完備係数拡大へ移し、有限橋の擬同型と両枠の比較を使う。

## 規約
古典的な余単体的代数と交代余面複体だけを扱う。

## 使われ方
BS 著者版 Theorem 6.4、D69 の結晶の橋の検収。
-/

public noncomputable section
open CategoryTheory AlgebraicTopology
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
local notation "D" => Functor.obj (bigCechAlexander P hP) T
local notation "E" => Functor.obj (wittBigPdModel P hpC hlocal) T
local notation "U" => fun n => affineEnvelopeTerm P hP T.n n (polyCutoff P T.n) le_rfl
local notation "ψ" => psiRing P hpA
local notation "F" => pCompletedScalarExtensionFunctor p ψ

private theorem bigTargetComplete (n : SimplexCategory) :
    IsModuleComplete W (p : W) ((E ⋙ PDCechNerve.algebraModule W).obj n) := by
  let : Algebra W C := (wZero p C).toAlgebra
  let Z := WittBigCrystalline.term P hpC hlocal T n.len
  let : Algebra W Z.carrier := (((E).obj n).hom).hom.toAlgebra
  change IsModuleComplete W (p : W) (ModuleCat.of W Z.carrier)
  apply (isModuleComplete_algebraMap_iff W Z.carrier (p : W) Z.carrier).mp
  rw [map_natCast]
  exact (wittBigCrystalline P hpC hlocal T n.len).complete_p

/-- 指定の大きい結晶の橋の、各項の完備係数変更後の標準余鎖写像。 -/
def wittBigCompletedBridge :
    ((F).mapHomologicalComplex _).obj
      ((alternatingCofaceMapComplex (ModuleCat.{u} A)).obj (D ⋙ PDCechNerve.algebraModule A)) ⟶
    (alternatingCofaceMapComplex (ModuleCat.{u} W)).obj (E ⋙ PDCechNerve.algebraModule W) := by
  let : Algebra A W := (ψ).toAlgebra
  exact completedUnderCechCoefficientCochainMap p A W D E
    ((wittBigBridge P hpA hpC hlocal hP).app T) (bigTargetComplete P hpC hlocal T)

private theorem finiteBigSquare :
    affineCechAlexanderFrame (P := P) hP T ≫ (wittBigBridge P hpA hpC hlocal hP).app T =
      WittFiniteBridge.finiteBridge P hpA hpC hlocal hC T U ≫
        Functor.whiskerRight (wittSmallFrame P hpC hlocal T hC)
          (Under.map (CommRingCat.ofHom ψ)) := by
  apply NatTrans.ext
  funext n
  obtain ⟨n⟩ := n
  apply Under.UnderMorphism.ext
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro x
  exact (WittFiniteBridge.finiteBridgeAt_frame P hpA hpC hlocal hC T n
    ((U) n) (affineBigCechTerm P T n hP) x).symm

/-- 大きい結晶の橋は、ψ による各項の完備係数変更後に擬同型となる。 -/
theorem wittBigCompletedBridge_quasiIso :
    QuasiIso (wittBigCompletedBridge P hpA hpC hlocal hP T) := by
  let : Algebra A W := (ψ).toAlgebra
  let a := (alternatingCofaceMapComplex (ModuleCat.{u} A)).map
    (Functor.whiskerRight (affineCechAlexanderFrame (P := P) hP T) (PDCechNerve.algebraModule A))
  let b := (alternatingCofaceMapComplex (ModuleCat.{u} W)).map
    (Functor.whiskerRight (wittSmallFrame P hpC hlocal T hC) (PDCechNerve.algebraModule W))
  let : QuasiIso (((F).mapHomologicalComplex _).map a) :=
    affineCechAlexanderFrame_map_quasiIso P hP T (F)
  let : QuasiIso b := wittSmallFrame_quasiIso P hpC hlocal T hC
  let : QuasiIso (wittFiniteCompletedCechBridge P hpA hpC hlocal hP T) :=
    wittFiniteCompletedCechBridge_quasiIso P hpA hpC hlocal hP T
  have hs := completedUnderCechCoefficientCochainMap_naturality p A W
    (polyCosimplicialAlgebra P hP T.n) (pdModel p W T.n)
    (WittFiniteBridge.finiteBridge P hpA hpC hlocal hC T U) (finiteTargetComplete P T)
    (affineCechAlexanderFrame (P := P) hP T) (wittSmallFrame P hpC hlocal T hC)
    ((wittBigBridge P hpA hpC hlocal hP).app T) (bigTargetComplete P hpC hlocal T)
    (finiteBigSquare P hpA hpC hlocal hP T)
  have hs' : ((F).mapHomologicalComplex _).map a ≫
      wittBigCompletedBridge P hpA hpC hlocal hP T =
      wittFiniteCompletedCechBridge P hpA hpC hlocal hP T ≫ b := hs
  have : QuasiIso (((F).mapHomologicalComplex _).map a ≫
      wittBigCompletedBridge P hpA hpC hlocal hP T) := by
    rw [hs']
    infer_instance
  exact quasiIso_of_comp_left (((F).mapHomologicalComplex _).map a) _

variable {T' : Poly (A ⧸ P.ideal)} (g : T ⟶ T')

/-- 完備係数変更後の大きい橋も多項式の射について厳密に自然。 -/
theorem wittBigCompletedBridge_naturality :
    ((F).mapHomologicalComplex _).map
        ((alternatingCofaceMapComplex (ModuleCat.{u} A)).map
          (Functor.whiskerRight ((bigCechAlexander P hP).map g) (PDCechNerve.algebraModule A))) ≫
      wittBigCompletedBridge P hpA hpC hlocal hP T' =
    wittBigCompletedBridge P hpA hpC hlocal hP T ≫
      (alternatingCofaceMapComplex (ModuleCat.{u} W)).map
        (Functor.whiskerRight ((wittBigPdModel P hpC hlocal).map g) (PDCechNerve.algebraModule W)) := by
  let : Algebra A W := (ψ).toAlgebra
  exact completedUnderCechCoefficientCochainMap_naturality p A W D E
    ((wittBigBridge P hpA hpC hlocal hP).app T) (bigTargetComplete P hpC hlocal T)
    ((bigCechAlexander P hP).map g) ((wittBigPdModel P hpC hlocal).map g)
    ((wittBigBridge P hpA hpC hlocal hP).app T') (bigTargetComplete P hpC hlocal T')
    ((wittBigBridge P hpA hpC hlocal hP).naturality g)

end SerrePositivity.BhattScholze.Prismatic
