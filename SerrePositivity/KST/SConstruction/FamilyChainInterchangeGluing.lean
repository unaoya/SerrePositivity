module
public import SerrePositivity.KST.SConstruction.FamilyChainInterchangeSquares
public import Mathlib.Data.List.Chain

/-! # 元の補正列に沿う交換正方形の隣接面の貼り合わせ
概要：各区間に作った交換正方形は、元の補正列の共有終始点に沿って厳密に貼り合う。
方針：元の実ホモトピーの終点と次の始点を、正方形の第一時刻の二面で回収する。
規約：内部の共有面を選び直さず、元の同じ適合円柱を保持する。
使われ方：合成補正の全 trace に沿う連続した二次元比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial

/-- 交換正方形列の隣接する第一時刻の終面・始面は、実写像として等しい。 -/
lemma familyHomotopyChainInterchangeSquares_glue {U E F G : SSet.{u}} {a b : U ⟶ E}
    (c : FamilyHomotopyChain a b) (k : U ⊗ (Δ[1] : SSet.{u}) ⟶ F) (m : E ⊗ F ⟶ G) :
    List.IsChain (fun s t => (SSet.ι₁ (X := U) ▷ (Δ[1] : SSet.{u})) ≫ s =
      (SSet.ι₀ (X := U) ▷ (Δ[1] : SSet.{u})) ≫ t)
      (familyHomotopyChainInterchangeSquares c k m) := by
  induction c with
  | nil => exact .nil
  | cons H tail ih =>
      cases tail with
      | nil => exact .singleton _
      | cons K rest =>
          refine .cons_cons ?_ ih
          change (SSet.ι₁ (X := U) ▷ (Δ[1] : SSet.{u})) ≫
              familyInterchangeSquare H.h k m =
            (SSet.ι₀ (X := U) ▷ (Δ[1] : SSet.{u})) ≫ familyInterchangeSquare K.h k m
          rw [familyInterchangeSquare_first_one, familyInterchangeSquare_first_zero, H.h₁, K.h₀]

end SerrePositivity.KST.SConstruction
