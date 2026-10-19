module
public import SerrePositivity.KST.SConstruction.FamilyInterchangeCylinderChains
public import SerrePositivity.KST.SConstruction.FamilyChainInterchangeSquares

/-! # 同じ実交換正方形の二時刻の交換
概要：円柱間の補正として使う正方形と、元の交換正方形の全体を厳密に同定する。
方針：同じ共通パラメータを固定し、二つの標準区間だけを交換する。
規約：正方形を選び直さず、四面と全単体を保持する。
使われ方：貼り合わせた二次元列の全セルを元の交換正方形列に照合する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial

/-- 共通パラメータを保ち、同じ正方形の二時刻だけを交換する。 -/
def familySquareClockSwap (U : SSet.{u}) :
    (U ⊗ (Δ[1] : SSet.{u})) ⊗ Δ[1] ⟶ (U ⊗ Δ[1]) ⊗ Δ[1] :=
  lift (lift (fst (U ⊗ Δ[1]) Δ[1] ≫ fst U Δ[1]) (snd (U ⊗ Δ[1]) Δ[1]))
    (fst (U ⊗ Δ[1]) Δ[1] ≫ snd U Δ[1])

/-- 二時刻の交換は、同じ実交換正方形の全体を回収する。 -/
lemma familyInterchangeSquare_clockSwap {U E F G : SSet.{u}}
    (h : U ⊗ (Δ[1] : SSet.{u}) ⟶ E) (k : U ⊗ (Δ[1] : SSet.{u}) ⟶ F)
    (m : E ⊗ F ⟶ G) :
    familySquareClockSwap U ≫ familyInterchangeSquare h k m =
      familyInterchangeSquare k h ((β_ F E).hom ≫ m) := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro x
  rfl

/-- 同じ交換正方形列は、二時刻だけを交換すると円柱間の補正全列になる。 -/
lemma familyInterchangeCylinderChain_trace_clockSwap {U E F G : SSet.{u}}
    {a b : U ⟶ E} (c : FamilyHomotopyChain a b)
    (k : U ⊗ (Δ[1] : SSet.{u}) ⟶ F) (m : E ⊗ F ⟶ G) :
    familyHomotopyChainTrace (familyInterchangeCylinderChain c k m) =
      (familyHomotopyChainInterchangeSquares c k m).map (familySquareClockSwap U ≫ ·) := by
  simp only [familyInterchangeCylinderChain_trace, familyHomotopyChainInterchangeSquares,
    List.map_map, Function.comp_def, familyInterchangeSquare_clockSwap]

/-- 二時刻の交換は、共通パラメータの制限と厳密に可換。 -/
lemma familySquareClockSwap_restrict {U V : SSet.{u}} (j : V ⟶ U) :
    ((j ▷ (Δ[1] : SSet.{u})) ▷ (Δ[1] : SSet.{u})) ≫ familySquareClockSwap U =
      familySquareClockSwap V ≫ ((j ▷ (Δ[1] : SSet.{u})) ▷ (Δ[1] : SSet.{u})) := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro x
  rfl

/-- 二時刻交換の第二 zero 面は、同じ元の第一 zero 面。 -/
lemma familySquareClockSwap_second_zero (U : SSet.{u}) :
    SSet.ι₀ ≫ familySquareClockSwap U = (SSet.ι₀ (X := U) ▷ (Δ[1] : SSet.{u})) := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro x
  rfl

/-- 二時刻交換の第一 zero 面は、同じ元の第二 zero 面。 -/
lemma familySquareClockSwap_first_zero (U : SSet.{u}) :
    (SSet.ι₀ (X := U) ▷ (Δ[1] : SSet.{u})) ≫ familySquareClockSwap U = SSet.ι₀ := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro x
  rfl

/-- 二時刻交換の第二 one 面は、同じ元の第一 one 面。 -/
lemma familySquareClockSwap_second_one (U : SSet.{u}) :
    SSet.ι₁ ≫ familySquareClockSwap U = (SSet.ι₁ (X := U) ▷ (Δ[1] : SSet.{u})) := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro x
  rfl

/-- 二時刻交換の第一 one 面は、同じ元の第二 one 面。 -/
lemma familySquareClockSwap_first_one (U : SSet.{u}) :
    (SSet.ι₁ (X := U) ▷ (Δ[1] : SSet.{u})) ≫ familySquareClockSwap U = SSet.ι₁ := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro x
  rfl

/-- 共通パラメータの制限後の第一 zero 面は、元の第二 zero 面の同じ制限。 -/
@[reassoc]
lemma familySquareClockSwap_first_zero_restrict {U V : SSet.{u}} (j : V ⟶ U) :
    (SSet.ι₀ (X := V) ▷ (Δ[1] : SSet.{u})) ≫
        ((j ▷ (Δ[1] : SSet.{u})) ▷ (Δ[1] : SSet.{u})) ≫ familySquareClockSwap U =
      (j ▷ (Δ[1] : SSet.{u})) ≫ SSet.ι₀ := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro x
  rfl

/-- 共通パラメータの制限後の第一 one 面は、元の第二 one 面の同じ制限。 -/
@[reassoc]
lemma familySquareClockSwap_first_one_restrict {U V : SSet.{u}} (j : V ⟶ U) :
    (SSet.ι₁ (X := V) ▷ (Δ[1] : SSet.{u})) ≫
        ((j ▷ (Δ[1] : SSet.{u})) ▷ (Δ[1] : SSet.{u})) ≫ familySquareClockSwap U =
      (j ▷ (Δ[1] : SSet.{u})) ≫ SSet.ι₁ := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro x
  rfl

end SerrePositivity.KST.SConstruction
