module

public import SerrePositivity.InfinityCategories.F1.FunctorCategories.RelativeFunctorRestrictionFibration

/-!
概要：二成分への同時写像の初期値 fiber で、第二成分の充填性を回収する。
方針：指定した初期成分と第二成分を組にして持ち上げ、同じ初期値 fiber へ戻す。
規約：同時写像の left fibration 性だけを使う。使われ方：固定初期値の終点評価。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
noncomputable section
variable {X D C : SSet.{u}} (f : X ⟶ D) (g : X ⟶ C) (d : D _⦋0⦌)

/-- 第一成分を同じ点で固定した fiber から、元の第二成分へ写す。 -/
def fixedFiberSecondMap : vertexFiber f d ⟶ C := vertexFiberι f d ≫ g

/-- 同時写像が left fibration なら、初期値を固定した第二成分も left fibration。 -/
instance fixedFiberSecondMap_leftFibration [LeftFibration (lift f g)] :
    LeftFibration (fixedFiberSecondMap f g d) where
  mem := by
    intro T U r hr
    have := LeftFibration.mem (p := lift f g) r hr
    constructor
    intro a b sq
    let b' := lift (SSet.const d : U ⟶ D) b
    have hs : CommSq (a ≫ vertexFiberι f d) r (lift f g) b' := by
      constructor
      apply CartesianMonoidalCategory.hom_ext
      · rw [Category.assoc, Category.assoc, lift_fst, Category.assoc, vertexFiberι_comp]
        change SSet.const d = r ≫ lift (SSet.const d : U ⟶ D) b ≫ fst D C
        rw [lift_fst, SSet.comp_const]
      · rw [Category.assoc, Category.assoc, lift_snd, Category.assoc, lift_snd]
        exact sq.w
    have hb : hs.lift ≫ f = SSet.const d := by
      have h := congrArg (fun k ↦ k ≫ fst D C) hs.fac_right
      simpa only [b', Category.assoc, lift_fst] using h
    let W := vertexFiberLift f d hs.lift hb
    refine CommSq.HasLift.mk' { l := W, fac_left := ?_, fac_right := ?_ }
    · apply vertexFiber_hom_ext f d
      rw [Category.assoc, vertexFiberLift_ι]
      exact hs.fac_left
    · change W ≫ vertexFiberι f d ≫ g = b
      dsimp only [W]
      rw [← Category.assoc, vertexFiberLift_ι]
      have h := congrArg (fun k ↦ k ≫ snd D C) hs.fac_right
      simpa only [b', Category.assoc, lift_snd] using h

end
end SerrePositivity.InfinityCategories.HomotopyLimits
