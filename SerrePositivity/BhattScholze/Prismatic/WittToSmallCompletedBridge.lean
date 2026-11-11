module

public import SerrePositivity.BhattScholze.Prismatic.PDCompletedCechBaseChange
public import SerrePositivity.BhattScholze.Prismatic.WittSmallFrameAdditiveQuasiIso
public import SerrePositivity.BhattScholze.Prismatic.WittToSmallFrame
import all SerrePositivity.BhattScholze.Prismatic.PDCompletedCechBaseChange
import all SerrePositivity.BhattScholze.Prismatic.CompletedCechCoefficientMap
import all SerrePositivity.BhattScholze.Prismatic.WittToSmall
import all SerrePositivity.BhattScholze.Prismatic.WittToSmallFrame
import all SerrePositivity.BhattScholze.Prismatic.PDPolynomialFunctor
import all SerrePositivity.BhattScholze.Prismatic.PDCompletedCech

/-!
# 第 0 Witt 成分の比較の完備係数変更後の擬同型

## 概要
指定された wittToSmall は、第 0 Witt 成分による各項の完備係数変更後に擬同型となる。

## 方針
有限枠では小さい分冪模型の標準係数射になる。枠の鎖ホモトピーを加法的関手で移して戻す。

## 規約
交代余面複体の古典的な射と多項式についての厳密な自然性を扱う。

## 使われ方
BS 著者版 Theorem 6.4、D69 の二つ目の Witt 比較の検収。
-/

public noncomputable section
open CategoryTheory AlgebraicTopology
open SerrePositivity.DerivedCompletion
universe u
namespace SerrePositivity.BhattScholze.Prismatic
set_option backward.isDefEq.respectTransparency false
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] (P : OrientedPrism p A)
variable (hpC : Function.Injective (fun x : A ⧸ P.ideal => (p : A ⧸ P.ideal) * x))
variable (hlocal : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A ⧸ P.ideal))
variable [hC : IsAdicComplete (Ideal.span {(p : A ⧸ P.ideal)}) (A ⧸ P.ideal)]
variable (T : Poly (A ⧸ P.ideal))
local notation "C" => A ⧸ P.ideal
local notation "W" => WittVector p C
local notation "γC" => residuePdStructure p hpC hlocal
local notation "D" => Functor.obj (wittBigPdModel P hpC hlocal) T
local notation "E" => Functor.obj
  (pdPolynomialFunctor p γC (Ideal.mem_span_singleton_self (p : C)) hC hpC) T
local notation "F" => pCompletedScalarExtensionFunctor p (wZero p C)

/-- 指定された第 0 Witt 成分の比較の、各項の完備係数変更後の余鎖写像。 -/
def wittToSmallCompletedBridge :
    ((F).mapHomologicalComplex _).obj
      ((alternatingCofaceMapComplex (ModuleCat.{u} W)).obj (D ⋙ PDCechNerve.algebraModule W)) ⟶
    (alternatingCofaceMapComplex (ModuleCat.{u} C)).obj (E ⋙ PDCechNerve.algebraModule C) := by
  let : Algebra W C := (wZero p C).toAlgebra
  exact completedUnderCechCoefficientCochainMap p W C D E
    ((wittToSmall P hpC hlocal hC).app T) (modelComplete p C T.n)

private theorem smallSquare :
    letI : Algebra W C := (wZero p C).toAlgebra
    wittSmallFrame P hpC hlocal T hC ≫ (wittToSmall P hpC hlocal hC).app T =
      pdModelBaseChange p W C T.n := by
  let : Algebra W C := (wZero p C).toAlgebra
  have h := wittToSmall_frame P hpC hlocal hC T
  change wittSmallFrame P hpC hlocal T hC ≫ (wittToSmall P hpC hlocal hC).app T ≫ 𝟙 _ =
    pdModelBaseChange p W C T.n at h
  simpa only [Category.comp_id] using h

/-- 第 0 Witt 成分の大きい枠の比較は、完備係数変更後に擬同型となる。 -/
theorem wittToSmallCompletedBridge_quasiIso :
    QuasiIso (wittToSmallCompletedBridge P hpC hlocal T) := by
  let : Algebra W C := (wZero p C).toAlgebra
  let a := (alternatingCofaceMapComplex (ModuleCat.{u} W)).map
    (Functor.whiskerRight (wittSmallFrame P hpC hlocal T hC) (PDCechNerve.algebraModule W))
  let : QuasiIso (((F).mapHomologicalComplex _).map a) :=
    wittSmallFrame_map_quasiIso P hpC hlocal T hC (F)
  have hs := completedUnderCechCoefficientCochainMap_naturality p W C
    (pdModel p W T.n) E (pdModelBaseChange p W C T.n) (modelComplete p C T.n)
    (wittSmallFrame P hpC hlocal T hC) (𝟙 E) ((wittToSmall P hpC hlocal hC).app T)
    (modelComplete p C T.n) (by
      simpa only [CategoryTheory.Functor.whiskerRight_id', Category.comp_id] using
        smallSquare P hpC hlocal T)
  simp only [CategoryTheory.Functor.whiskerRight_id', CategoryTheory.Functor.map_id,
    Category.comp_id] at hs
  have hs' : ((F).mapHomologicalComplex _).map a ≫
      wittToSmallCompletedBridge P hpC hlocal T = pdCompletedCechBaseChange p W C T.n := hs
  have : QuasiIso (((F).mapHomologicalComplex _).map a ≫
      wittToSmallCompletedBridge P hpC hlocal T) := by
    rw [hs']
    exact pdCompletedCechBaseChange_quasiIso p W C T.n
  exact quasiIso_of_comp_left (((F).mapHomologicalComplex _).map a) _

variable {T' : Poly (A ⧸ P.ideal)} (g : T ⟶ T')

/-- 完備係数変更後の第 0 成分の比較も、多項式の射について厳密に自然。 -/
theorem wittToSmallCompletedBridge_naturality :
    ((F).mapHomologicalComplex _).map
        ((alternatingCofaceMapComplex (ModuleCat.{u} W)).map
          (Functor.whiskerRight ((wittBigPdModel P hpC hlocal).map g) (PDCechNerve.algebraModule W))) ≫
      wittToSmallCompletedBridge P hpC hlocal T' =
    wittToSmallCompletedBridge P hpC hlocal T ≫
      (alternatingCofaceMapComplex (ModuleCat.{u} C)).map
        (Functor.whiskerRight
          ((pdPolynomialFunctor p γC (Ideal.mem_span_singleton_self (p : C)) hC hpC).map g)
          (PDCechNerve.algebraModule C)) := by
  let : Algebra W C := (wZero p C).toAlgebra
  exact completedUnderCechCoefficientCochainMap_naturality p W C D E
    ((wittToSmall P hpC hlocal hC).app T) (modelComplete p C T.n)
    ((wittBigPdModel P hpC hlocal).map g)
    ((pdPolynomialFunctor p γC (Ideal.mem_span_singleton_self (p : C)) hC hpC).map g)
    ((wittToSmall P hpC hlocal hC).app T') (modelComplete p C T'.n)
    ((wittToSmall P hpC hlocal hC).naturality g)

end SerrePositivity.BhattScholze.Prismatic
