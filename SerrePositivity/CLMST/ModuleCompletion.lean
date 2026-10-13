module

public import SerrePositivity.CommutativeAlgebra.RootTower.Completion
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.Torsion

/-! # CLMST の長さの定義域にある加群の導来 p 完備性

p が基底環の極大イデアルに属するとき、完備化した根の塔上の一様な
m_A 冪ねじれ加群は導来 p 完備である。Caution 2.4.4 の暗黙の条件を
具体的な導来対象について確認する。長さや almost の文献結果は使わない。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.CLMST
open CategoryTheory IsLocalRing
open Section2

/-- CLMST の m_A 冪ねじれ加群は導来 p 完備。
基底環での p の極大イデアル所属を完備化へ移し、一様な冪ねじれを使う。 -/
theorem isModuleComplete_of_completedTower_powTorsion
    (A : Type u) [CommRing A] [IsLocalRing A]
    {h : ℕ} (t : Fin h → A) (p : ℕ) (hp : (p : A) ∈ maximalIdeal A)
    (M : ModuleCat.{u} (CompletedTower A t p))
    (hM : IsPowTorsion (completedTowerMaxIdeal A t p) M) :
    DerivedCompletion.IsModuleComplete (CompletedTower A t p) (p : CompletedTower A t p) M := by
  apply DerivedCompletion.isModuleComplete_of_isPowTorsion
    (CompletedTower A t p) (completedTowerMaxIdeal A t p) _ _ M hM
  simpa [completedTowerMaxIdeal] using Ideal.mem_map_of_mem (algebraMap A (CompletedTower A t p)) hp

end SerrePositivity.CLMST
