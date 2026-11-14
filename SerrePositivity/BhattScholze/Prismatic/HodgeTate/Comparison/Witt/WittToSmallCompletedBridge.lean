module
public meta import SerrePositivity.Util.Citation

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.Comparison.PDCompletedCechBaseChange
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.WittSmallFrameAdditiveQuasiIso
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.WittToSmallFrame
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.Comparison.PDCompletedCechBaseChange
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.CompletedCechCoefficientMap
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.WittToSmall
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.WittToSmallFrame
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.Comparison.PDPolynomialFunctor
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.PDCompletedCech

/-!
# 第 0 Witt 成分の比較の完備係数変更後の擬同型

## 概要
指定された wittToSmall は、第 0 Witt 成分による各項の完備係数変更後に擬同型となる。

## 方針
有限枠では小さい分冪模型の標準係数射になる。枠の鎖ホモトピーを加法的関手で移して戻す。

## 規約
交代余面複体の古典的な射と多項式についての厳密な自然性を扱う。

## 使われ方
BS 著者版 Theorem 6.4 のWitt 係数から小さい模型への比較。
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

/-! Reviewed literature correspondences. -/
attribute [cite BS19 "Thm 6.4" (partial := component) "Witt の結晶 prism と、普遍基底での比較の部品（BS-D69 P2）。関手としての同型（D69）の組み立ては drafts ／ 11-11 更新。Witt 系は A と A/I が p 正則な一般の有界向き付き prism について作られている ／ 11-12 夜更新（§5・§6 の見直し）"] _root_.SerrePositivity.BhattScholze.Prismatic.wittToSmallCompletedBridge_quasiIso
