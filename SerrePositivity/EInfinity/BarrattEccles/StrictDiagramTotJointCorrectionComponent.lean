module

public import SerrePositivity.EInfinity.BarrattEccles.StrictDiagramTotJointPairingCorrection
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.TwistedArrowHomComposition

/-!
概要：元の corrected pairing の同じ指定同型の成分の三辺の合成則。
方針：元の成分自身へ既存の twisted-arrow のホモトピー圏の射の合成則を適用する。
規約：元の全同型の成分を保持する。全族の照合や弱同値性の結論ではない。
使われ方：元の source-frame 単位の像を左右の同じ端点の比較で計算する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory HomotopicalAlgebra SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans
open SerrePositivity.InfinityCategories.HA.StableInfinityCategories
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors
variable (A : Type u) [CommRing A]
local instance jointCorrectionComponentModel : ModelCategory (operad A).Algebra := modelCategory A
local instance jointCorrectionComponentFactorization :
    (cofibrations (operad A).Algebra).HasFunctorialFactorization
      (trivialFibrations (operad A).Algebra) := ⟨⟨mappingCofibrantFactorization A⟩⟩

/-- 元の全補正同型の同じ成分の左右射影と、元の二頂点の辺は合成等式を満たす。 -/
theorem strictBETotJointSourceCorrection_component_composition
    (t : StrictBETotJointSourceElements A) :
    let a := (strictBETotJointSourceCorrectedPairing A).app (Opposite.op ⦋0⦌) (nerveVertex t)
    let b := (strictBETotJointSourceNativePairing A).app (Opposite.op ⦋0⦌) (nerveVertex t)
    let f := ((strictBETotJointSourceCorrectedPairingIso A).app (nerveVertex t)).hom
    ((homotopyOppositeEquivalence (CAlg_R A)).functor.map
      ((SSet.mapHomotopyCategory (edgewiseLeft (CAlg_R A))).map f)).unop ≫
        HomotopyCategory.homMk (twistedArrowVertexEdge a) ≫
          (SSet.mapHomotopyCategory (edgewiseRight (CAlg_R A))).map f =
            HomotopyCategory.homMk (twistedArrowVertexEdge b) := by
  dsimp only
  exact twistedArrowHom_composition _

end SerrePositivity.EInfinity.BarrattEccles
