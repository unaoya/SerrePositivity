module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.AffineCochainMap
public import SerrePositivity.HomologicalAlgebra.ProductTotalSingleRow
public import Mathlib.Algebra.Homology.Embedding.ExtendHomology

/-!
# affine Hodge–Tate 余鎖模型の指定された積全複体

## 概要
係数線形な余鎖複体を整数次数へ零延長し、縦次数零に集中させた積全複体として表示する。

## 方針
既存の単一行の積全複体の同型と、零延長のホモロジー同型を使う。

## 規約
元のコホモロジーと標準ηを指定された同型で移す。比較定理の結論を前提にしない。

## 使われ方
BS 著者版 Proposition 6.2 の古典的な模型と Lemma 4.22 の積全複体模型の接続。
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
open CategoryTheory HomologicalComplex
open SerrePositivity.HomologicalAlgebra

namespace SerrePositivity.BhattScholze.Prismatic

variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]
  (P : OrientedPrism p A) (hP : IsBoundedPrism P) (r : ℕ)

/-- 元の非負余鎖複体の整数次数への零延長。 -/
abbrev affineHTExtendedComplex : CochainComplex (ModuleCat.{u} (affineAlgebra P r)) ℤ :=
  (affineHTComplex P hP r).extend ComplexShape.embeddingUpNat

/-- 同じ余鎖模型を縦次数零に集中させた厳密な二重複体。 -/
abbrev affineHTTotalDiagram :
    HomologicalComplex₂ (ModuleCat.{u} (affineAlgebra P r)) (.up ℤ) (.up ℤ) :=
  (ProductTotal.singleRowFunctor (ModuleCat.{u} (affineAlgebra P r))).obj
    (affineHTExtendedComplex P hP r)

/-- 指定された積全複体模型。 -/
abbrev affineHTTotalComplex : CochainComplex (ModuleCat.{u} (affineAlgebra P r)) ℤ :=
  (ProductTotal.functor (ModuleCat.{u} (affineAlgebra P r))).obj
    (affineHTTotalDiagram P hP r)

/-- 各次数の唯一の縦次数零の成分への指定射影による同型。 -/
def affineHTTotalIso : affineHTTotalComplex P hP r ≅ affineHTExtendedComplex P hP r :=
  ProductTotal.singleRowIso (affineHTExtendedComplex P hP r)

/-- 指定射影と零延長による、元の係数線形ホモロジーへの同型。 -/
def affineHTTotalHomologyIso (n : ℕ) :
    (affineHTTotalComplex P hP r).homology (n : ℤ) ≅
      (affineHTComplex P hP r).homology n :=
  (homologyFunctor _ (.up ℤ) (n : ℤ)).mapIso (affineHTTotalIso P hP r) ≪≫
    (affineHTComplex P hP r).extendHomologyIso ComplexShape.embeddingUpNat rfl

/-- 係数作用も保った、元の Hodge–Tate コホモロジーとの同一視。 -/
def affineHTTotalCohomologyEquiv (n : ℕ) :
    letI := htModule P hP r n
    hodgeTateCohomology' P hP r n ≃ₗ[affineAlgebra P r]
      (affineHTTotalComplex P hP r).homology (n : ℤ) :=
  (affineHTCohomologyEquiv P hP r n).trans
    (affineHTTotalHomologyIso P hP r n).symm.toLinearEquiv

/-- 元の標準ηを、指定された積全複体の同じホモロジーへ送る。 -/
def affineHTTotalMap (n : ℕ) :
    affineForms P r n →ₗ[affineAlgebra P r]
      (affineHTTotalComplex P hP r).homology (n : ℤ) :=
  (affineHTTotalHomologyIso P hP r n).inv.hom.comp (affineHTMap P hP r n)

/-- 指定射影で戻すと、標準の係数線形ηそのものになる。 -/
theorem affineHTTotalMap_projection (n : ℕ) (x : affineForms P r n) :
    (affineHTTotalHomologyIso P hP r n).hom (affineHTTotalMap P hP r n x) =
      affineHTMap P hP r n x := by
  exact (affineHTTotalHomologyIso P hP r n).toLinearEquiv.apply_symm_apply _

/-- 全複体での全単射性は元の標準ηの全単射性と同値である。 -/
theorem affineHTTotalMap_bijective_iff (n : ℕ) :
    Function.Bijective (affineHTTotalMap P hP r n) ↔
      Function.Bijective (affineHTMap P hP r n) := by
  let E := (affineHTTotalHomologyIso P hP r n).symm.toLinearEquiv
  let f := affineHTMap P hP r n
  change Function.Bijective (fun x => E (f x)) ↔ Function.Bijective f
  constructor
  · rintro ⟨hinj, hsurj⟩
    constructor
    · intro x y h
      exact hinj (congrArg E h)
    · intro y
      obtain ⟨x, hx⟩ := hsurj (E y)
      exact ⟨x, E.injective hx⟩
  · intro h
    exact E.bijective.comp h

/-- 目標の古典的な型を、同じ積全複体の標準ηで判定する。 -/
theorem hodgeTateIsoStatement_iff_affineHTTotalMap_bijective :
    HodgeTateIsoStatement P hP r ↔ ∀ n, Function.Bijective (affineHTTotalMap P hP r n) := by
  rw [hodgeTateIsoStatement_iff_affineHTMap_bijective]
  exact forall_congr' (fun n => (affineHTTotalMap_bijective_iff P hP r n).symm)

end SerrePositivity.BhattScholze.Prismatic
