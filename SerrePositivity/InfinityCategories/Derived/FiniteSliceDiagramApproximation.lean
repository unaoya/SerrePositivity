module
public import SerrePositivity.InfinityCategories.Derived.FiniteHomotopyRelativeFillers
public import SerrePositivity.InfinityCategories.Derived.FiniteTerminalMappingCone
public import SerrePositivity.InfinityCategories.Derived.RightFibrationHomotopyLift
public import SerrePositivity.InfinityCategories.Derived.PullbackDiagramHomotopy
public import SerrePositivity.InfinityCategories.Stable.SpanHomotopyGluing
public import SerrePositivity.InfinityCategories.F1B.HomotopyWhiskering

/-! # slice 型引き戻しの有限図式の錐への比較

概要：有限対充填を持つ射を終対象付き右ファイブレーションへ引き戻し、有限図式を錐へ結ぶ。
方針：終対象方向の写像錐を充填し、商比較を右ファイブレーションへ終端から持ち上げる。
規約：元・商比較の境界整合式を全時刻で用いる。使われ方：Quillen A の弱可縮性検査。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial

/-- 終対象付き右ファイブレーションへの引き戻し内の有限図式は、錐を持つ図式へ比較できる。 -/
lemma HasFiniteHomotopyRelativeFillers.finitePullbackConeApproximation
    {E Y Q : SSet.{u}} {F : E ⟶ Q} (hF : HasFiniteHomotopyRelativeFillers F)
    (p : Y ⟶ Q) [RightFibration p] {x : Y _⦋0⦌} (hx : IsTerminalVertex x)
    {K : SSet.{u}} [K.Finite] (d : K ⟶ pullback F p) :
    ∃ w : finiteMappingCylinder (finiteConeMap K) ⟶ pullback F p,
      Nonempty (SSet.Homotopy (finiteMappingCylinderSource (finiteConeMap K) ≫ w) d) := by
  let i := finiteMappingCylinderSource (finiteConeMap K)
  let a := d ≫ pullback.fst F p
  obtain ⟨G, hG⟩ := hx.finiteCone_extension (d ≫ pullback.snd F p)
  have ha : a ≫ F = i ≫ G ≫ p := by
    rw [← Category.assoc, hG]
    dsimp only [a]
    rw [Category.assoc, pullback.condition, ← Category.assoc]
  obtain ⟨R⟩ := hF i a (G ≫ p) ha
  obtain ⟨v, T, hv, hT⟩ := rightFibration_lift_end_homotopy p G R.comparison rfl
  let w := pullback.lift R.filler v hv.symm
  let A : SSet.Homotopy ((i ≫ w) ≫ pullback.fst F p) (d ≫ pullback.fst F p) :=
    stableHomotopyRetarget R.boundary (by
      dsimp only [w]
      rw [Category.assoc, pullback.lift_fst]) rfl
  let B : SSet.Homotopy ((i ≫ w) ≫ pullback.snd F p) (d ≫ pullback.snd F p) :=
    stableHomotopyRetarget (functorHomotopyPrecomp T i) (by
      dsimp only [w]
      rw [Category.assoc, pullback.lift_snd]) hG
  have hc : A.h ≫ F = B.h ≫ p := by
    change R.boundary.h ≫ F = ((i ▷ (Δ[1] : SSet.{u})) ≫ T.h) ≫ p
    rw [Category.assoc, hT]
    exact R.compatibility.symm
  exact ⟨w, ⟨pullbackDiagramHomotopy F p A B hc⟩⟩

end SerrePositivity.InfinityCategories
