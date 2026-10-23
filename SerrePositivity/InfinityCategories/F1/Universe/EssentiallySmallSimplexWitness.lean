module

public import SerrePositivity.InfinityCategories.F1.Universe.EssentiallySmallPointWitness
public import SerrePositivity.InfinityCategories.F1.Universe.EssentiallySmallFibersBaseChange
public import SerrePositivity.InfinityCategories.F1.Transport.SimplexDimensionStep

/-!
概要：essentially small fiber の標準単体上の表現空間を、低次元の可縮性から構成する。
方針：点では小さい Kan 模型を用い、区間と高次の内ホーンでは既存の相対充填へ渡す。
規約：元の全空間と次数 fiber の小ささは仮定しない。
使われ方：任意の底の相対表現のための有限次元帰納法。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

local instance essentiallySmallSimplexPullbackSndLF {E B D : SSet.{u + 1}}
    (p : E ⟶ B) [LeftFibration p] (g : D ⟶ B) :
    LeftFibration (pullback.snd p g) :=
  ⟨leftFibrations.pullback_snd p g (LeftFibration.mem (p := p))⟩

/-- 小さい Kan 模型を持つ fiber だけを仮定した、標準単体上の次元帰納法の一段。 -/
lemma essentiallySmallSimplexWitnessSpace_isContractibleKan_of_lowerDimension (n : ℕ)
    (ih : ∀ {E B : SSet.{u + 1}} (p : E ⟶ B) [LeftFibration p] [B.HasDimensionLT n],
      HasEssentiallySmallFibers p → IsContractibleKan (transportWitnessSpace p))
    {E : SSet.{u + 1}} (p : E ⟶ (Δ[n] : SSet.{u + 1})) [LeftFibration p]
    (hp : HasEssentiallySmallFibers p) : IsContractibleKan (transportWitnessSpace p) := by
  rcases n with _ | n
  · exact essentiallySmallPointTransportWitnessSpace_isContractibleKan p hp
  rcases n with _ | n
  · have := intervalWitnessRestriction_trivialKanFibration p
    exact isContractibleKan_of_trivialKanFibration (transportWitnessRestriction p (boundary 1).ι)
      (ih (pullback.snd p (boundary 1).ι) (hp.pullback_snd (boundary 1).ι))
  · let j : Fin (n + 3) := 1
    have hj : innerAnodyneExtensions (horn (n + 2) j).ι :=
      innerAnodyneExtensions.horn_ι (by
        change 0 < 1 % (n + 3)
        rw [Nat.mod_eq_of_lt (by omega)]
        omega) (by
        change 1 % (n + 3) < n + 2
        rw [Nat.mod_eq_of_lt (by omega)]
        omega)
    have := transportWitnessRestriction_trivialKanFibration_of_innerAnodyne p
      (horn (n + 2) j).ι hj
    exact isContractibleKan_of_trivialKanFibration
      (transportWitnessRestriction p (horn (n + 2) j).ι)
      (ih (pullback.snd p (horn (n + 2) j).ι) (hp.pullback_snd (horn (n + 2) j).ι))

end SerrePositivity.InfinityCategories
