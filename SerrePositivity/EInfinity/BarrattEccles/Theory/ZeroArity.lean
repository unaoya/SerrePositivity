module

public import SerrePositivity.EInfinity.BarrattEccles.Basis
public import SerrePositivity.EInfinity.BarrattEccles.Contraction
public import SerrePositivity.EInfinity.BarrattEccles.Theory.ConcentratedHomotopy

/-!
# Barratt–Eccles の零入力の次数

## 概要
BF §1.1.1–1.1.2 の E(0) は次数零に集中する。

## 方針
零入力の置換群は一点なので、正の単体次数に非退化単体はない。既存の基底へ移す。

## 規約
基礎環は任意の可換環であり、加群の非自明性は仮定しない。

## 使われ方
HA 3.2.4.7 のテンソル代数の包含に使う零入力の単位。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory Limits DifferentialGraded
variable (A : Type u) [CommRing A]

/-- BF §1.1.1 の零入力には正次数の非退化単体がない。 -/
lemma zeroArity_nondegenerate_isEmpty (q : ℕ) (hq : 0 < q) :
    IsEmpty ((simplicial 0).nonDegenerate q) := by
  refine ⟨fun x => ?_⟩
  exact ((mem_nonDegenerate_iff 0 q x.val).mp x.property) ⟨0, hq⟩ (Subsingleton.elim _ _)

/-- BF §1.1.2 の E(0) は負次数で零である。 -/
lemma zeroArity_isZero_negative (q : ℕ) (hq : 0 < q) :
    IsZero ((complex A 0).X (-(q : ℤ))) := by
  letI := zeroArity_nondegenerate_isEmpty q hq
  letI : Subsingleton ((complex A 0).X (-(q : ℤ))) := by
    constructor
    intro x y
    apply (complexBasis A 0 q).repr.injective
    exact Subsingleton.elim _ _
  exact ModuleCat.isZero_of_subsingleton _

/-- BF §1.1.2 の零入力の複体は次数零以外で零である。 -/
lemma zeroArity_isZero_nonzero (i : ℤ) (hi : i ≠ 0) :
    IsZero ((complex A 0).X i) := by
  by_cases hp : 0 < i
  · exact complex_isZero_positive A 0 i hp
  · let q := (-i).toNat
    have he : -(q : ℤ) = i := by dsimp [q]; omega
    have hq : 0 < q := by dsimp [q]; omega
    rw [← he]
    exact zeroArity_isZero_negative A q hq

/-- BF §1.1.2 の零入力の増大は、鎖ホモトピー同値に加えて厳密な同型である。 -/
lemma zeroArity_augmentation_isIso : IsIso (complexAugmentation A 0) := by
  let e := isoOfHomotopyEquivConcentrated (j := (0 : ℤ)) (by simp)
    (zeroArity_isZero_nonzero A)
    (fun i hi => HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 _ i hi)
    (complexContraction A 0)
  exact e.isIso_hom

end SerrePositivity.EInfinity.BarrattEccles
