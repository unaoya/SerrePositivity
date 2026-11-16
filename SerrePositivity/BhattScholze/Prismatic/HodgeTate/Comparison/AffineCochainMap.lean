module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.AffineCochainModel
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Affine.HodgeTateCompletedMap
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Affine.HodgeTateCompletedMap

/-!
# 同じ Hodge–Tate 写像を係数線形複体のホモロジーへ移す

## 概要
既存の標準写像 η を、指定されたコホモロジー同型の後で評価する。

## 方針
次数零・一と積との可換性を既存の HTAlgebraMap の法則から移す。

## 規約
任意の同型への置換ではなく、元の η の同型性と厳密に同値な判定を与える。

## 使われ方
BS 著者版 Proposition 6.2 の標準写像の古典的な比較。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
open CategoryTheory
open SerrePositivity.Cosimplicial

namespace SerrePositivity.BhattScholze.Prismatic

variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]
  (P : OrientedPrism p A) (hP : IsBoundedPrism P) (r : ℕ)

/-- 元の標準 η を、同じ係数線形複体のホモロジーへ送った写像。 -/
def affineHTMap (n : ℕ) :
    affineForms P r n →ₗ[affineAlgebra P r] (affineHTComplex P hP r).homology n := by
  letI := htModule P hP r n
  exact (affineHTCohomologyEquiv P hP r n).toLinearMap.comp ((hodgeTateMap P hP r).app n)

/-- 次数零の比較は既存の η⁰ そのものである。 -/
theorem affineHTMap_on_zero (a : affineAlgebra P r) :
    affineHTMap P hP r 0 (degreeZeroForm P r a) =
      affineHTCohomologyEquiv P hP r 0 (hodgeTateMapZero P hP r a) := by
  change affineHTCohomologyEquiv P hP r 0
    ((hodgeTateMap P hP r).app 0 (degreeZeroForm P r a)) = _
  rw [(hodgeTateMap P hP r).on_zero]

/-- 次数一の比較も、選び直さず既存の η¹ を移したものである。 -/
theorem affineHTMap_on_one (x : affineForms P r 1) :
    affineHTMap P hP r 1 x =
      affineHTCohomologyEquiv P hP r 1 (hodgeTateMapOne P hP r x) := by
  change affineHTCohomologyEquiv P hP r 1 ((hodgeTateMap P hP r).app 1 x) = _
  rw [(hodgeTateMap P hP r).on_one]

/-- 完備形式の外積は、同じ模型の余鎖積へ移る。 -/
theorem affineHTMap_product {i j : ℕ} (x : affineForms P r i) (y : affineForms P r j) :
    affineHTMap P hP r (i+j) (affineWedge P r x y) =
      (affineHTCup P hP r).onHomology (affineHTMap P hP r i x) (affineHTMap P hP r j y) := by
  change affineHTCohomologyEquiv P hP r (i+j)
    ((hodgeTateMap P hP r).app (i+j) (affineWedge P r x y)) = _
  rw [(hodgeTateMap P hP r).product]
  exact affineHTCohomologyEquiv_cup P hP r _ _

/-- この模型上の判定と元の標準 η の全単射性は同値である。 -/
theorem affineHTMap_bijective_iff (n : ℕ) :
    Function.Bijective (affineHTMap P hP r n) ↔
      Function.Bijective ((hodgeTateMap P hP r).app n) := by
  let E := affineHTCohomologyEquiv P hP r n
  let f := (hodgeTateMap P hP r).app n
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

/-- 目標の古典的な型は、同じ複体模型の全次数の判定へ戻せる。 -/
theorem hodgeTateIsoStatement_iff_affineHTMap_bijective :
    HodgeTateIsoStatement P hP r ↔ ∀ n, Function.Bijective (affineHTMap P hP r n) := by
  unfold HodgeTateIsoStatement
  constructor
  · intro h n
    exact (affineHTMap_bijective_iff P hP r n).mpr (h n)
  · intro h n
    exact (affineHTMap_bijective_iff P hP r n).mp (h n)

end SerrePositivity.BhattScholze.Prismatic
