module
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ConeHomCoordinates
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexShift

/-! # シフトした mapping cone への Hom の fiber 座標

概要：標準 fiber への斉次 cochain を元の二成分と一段低いホモトピー成分へ分解する。
方針：右シフトの線形同値と cone の射影座標を合成し、第二座標の符号を反転する。
規約：HTT §1.2.13、N7.1 の fiber の微分。使われ方：N7c の全次数の明示的な充填。

対応節は Kerodon 2.5（Tag 00ND）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u

namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories

open CategoryTheory DifferentialGraded CochainComplex HomComplex

variable {A : Type u} [CommRing A] {X B D : Complex A}

/-- 概要：複体の射の標準 fiber は mapping cone の −1 シフト。
方針：既存の mappingCone と既存の整数シフトをそのまま使う。
規約：HTT §1.2.13、N7.1。使われ方：標準引き戻し錐の頂点。 -/
abbrev standardFiber (f : B ⟶ D) : Complex A := (mappingCone f)⟦(-1 : ℤ)⟧

/-- 概要：標準 fiber への Hom の全次数の A 線形座標。
方針：シフトを戻して fst・snd と合成し、snd 座標を負にする。
規約：N7.1 の fiber の微分 δ(u,z)=(δu,fu−δz)。使われ方：直接の線形充填の解。 -/
def fiberHomCoordinates (f : B ⟶ D) (n : ℤ) :
    Cochain X (standardFiber f) (n + 1) ≃ₗ[A] (Cochain X B (n + 1) × Cochain X D n) :=
  ((Cochain.rightShiftLinearEquiv A X (mappingCone f) n (-1) (n + 1) (by omega)).symm.trans
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coneHomCoordinates f n)).trans ((LinearEquiv.refl A _).prodCongr (LinearEquiv.neg A))

/-- 概要：fiber Hom の第一座標はシフトを戻した cochain の fst 成分。
方針：合成した線形同値を評価する。
規約：HTT §1.2.13、N7.1。使われ方：標準 fiber の射影の計算。 -/
lemma fiberHomCoordinates_fst (f : B ⟶ D) (n : ℤ) (a : Cochain X (standardFiber f) (n + 1)) :
    (fiberHomCoordinates f n a).1 =
      (a.rightUnshift n (by omega)).comp (mappingCone.fst f).val rfl := rfl

/-- 概要：fiber Hom の第二座標はシフトを戻した snd 成分の負。
方針：第二成分を負にする線形同値を評価する。
規約：HTT §1.2.13、N7.1。使われ方：標準 fiber のホモトピー成分の計算。 -/
lemma fiberHomCoordinates_snd (f : B ⟶ D) (n : ℤ) (a : Cochain X (standardFiber f) (n + 1)) :
    (fiberHomCoordinates f n a).2 =
      -((a.rightUnshift n (by omega)).comp (mappingCone.snd f) (add_zero n)) := rfl

/-- 概要：fiber Hom の逆座標写像は符号を付けた liftCochain の右シフト。
方針：線形同値の逆写像を評価する。
規約：HTT §1.2.13、N7.1。使われ方：全次数の明示解を実際の Hom へ戻す。 -/
lemma fiberHomCoordinates_symm (f : B ⟶ D) (n : ℤ)
    (a : Cochain X B (n + 1) × Cochain X D n) :
    (fiberHomCoordinates f n).symm a =
      (mappingCone.liftCochain f a.1 (-a.2) rfl).rightShift (-1) (n + 1) (by omega) := rfl

/-- 概要：fiber の逆座標写像は δ(u,z)=(δu,fu−δz) という微分と可換。
方針：右シフトの微分の負号と δ_liftCochain の式を展開して符号を相殺する。
規約：HTT §1.2.13、N7.1。使われ方：Hom-fiber の厳密な複体としての比較。 -/
lemma fiberHomCoordinates_symm_differential (f : B ⟶ D) (n : ℤ)
    (a : Cochain X B (n + 1)) (b : Cochain X D n) :
    δ (n + 1) (n + 1 + 1) ((fiberHomCoordinates f n).symm (a, b)) =
      (fiberHomCoordinates f (n + 1)).symm
        (δ (n + 1) (n + 1 + 1) a,
          a.comp (Cochain.ofHom f) (add_zero (n + 1)) - δ n (n + 1) b) := by
  rw [fiberHomCoordinates_symm, fiberHomCoordinates_symm,
    Cochain.δ_rightShift _ (-1) (n + 1) (n + 1 + 1) (by omega) (n + 1) (by omega),
    mappingCone.δ_liftCochain f a (-b) rfl (n + 1 + 1) rfl]
  simp only [show (-1 : ℤ).negOnePow = (-1 : ℤˣ) from by decide,
    Units.neg_smul, one_smul, ← Cochain.rightShift_neg]
  congr 1
  simp only [mappingCone.liftCochain, δ_neg, Cochain.neg_comp,
    Cochain.add_comp, neg_add_rev, neg_neg, sub_eq_add_neg]
  abel

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
