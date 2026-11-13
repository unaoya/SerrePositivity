module

public import SerrePositivity.EInfinity.PowerOperation.ConeFiberHomotopyComparison
public import SerrePositivity.EInfinity.PowerOperation.PointedConnectingComparison
public import SerrePositivity.EInfinity.PowerOperation.EilenbergMacLaneLoopTrivialFibration

/-!
# 指定 Γ 構造射の Ω 条件の次数移動

DAG XIII §2.2 のスペクトル忘却への前段。恒等 cone の実際の fiber と
指定随伴構造射の自然性から、隣接次数の全単射性を同値で結ぶ。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.PowerOperation
open CategoryTheory CategoryTheory.Limits CochainComplex SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open SerrePositivity.DifferentialGraded
open SerrePositivity.KST.Spectra (pointedHomotopyMap)
variable (A : Type u) [CommRing A]

/-- 指定構造射の全単射性を、元の複体の一つシフトと一つ上の次数へ移す。 -/
lemma gammaAdjointSuspension_bijective_iff_shift (M : Complex A) (n : ℕ) :
    Function.Bijective (pointedHomotopyMap n ((gammaAdjointSuspension A).app M)) ↔
      Function.Bijective (pointedHomotopyMap (n + 1)
        ((gammaAdjointSuspension A).app (M⟦(1 : ℤ)⟧))) := by
  have := gammaPointedFunctor_preservesFiniteLimits A
  have := gammaPointedFunctor_preservesZeroMorphisms A
  have := gammaLoopFunctor_preservesFiniteLimits A
  have := gammaLoopFunctor_preservesZeroMorphisms A
  let p := (gammaPointedFunctor A).map (mappingCone.triangle (𝟙 M)).mor₃
  let q := (gammaLoopFunctor A).map (mappingCone.triangle (𝟙 M)).mor₃
  have : Fibration p.right := gammaConeProjection_fibration A (𝟙 M)
  have : Fibration q.right := gammaLoopMap_fibration A _
    (coneProjection_projectiveFibration A (𝟙 M))
  have hf := coneFiberHomotopyMap_bijective_iff A (gammaPointedFunctor A)
    (gammaLoopFunctor A) (gammaAdjointSuspension A) (𝟙 M) n
  have hc := pointedConnecting_bijective_iff p q
    ((gammaAdjointSuspension A).app (mappingCone (𝟙 M)))
    ((gammaAdjointSuspension A).app (M⟦(1 : ℤ)⟧))
    ((gammaAdjointSuspension A).naturality (mappingCone.triangle (𝟙 M)).mor₃)
    (fun r => gammaIdentityCone_homotopy_subsingleton A M r _)
    (fun r => gammaLoopIdentityCone_homotopy_subsingleton A M r _)
    (gammaIdentityCone_terminal_rlp A M) (gammaLoopIdentityCone_terminal_rlp A M) n
  exact hf.trans hc

end SerrePositivity.EInfinity.PowerOperation
