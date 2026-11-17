module

public import SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.StrictDiagramTotJointPairingCorrection
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.TwistedArrowHomComposition

/-!
状態：D81により停止したBE模型のIS-W2 Tot経路。既存の到達点の保管用。
概要：元の corrected pairing の同じ指定同型の成分の三辺の合成則。
方針：元の成分自身へ既存の twisted-arrow のホモトピー圏の射の合成則を適用する。
規約：元の全同型の成分を保持する。全族の照合や弱同値性の結論ではない。
使われ方：元の source-frame 単位の像を左右の同じ端点の比較で計算する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot
open _root_.CategoryTheory _root_.HomotopicalAlgebra _root_.SSet
open scoped _root_.Simplicial
open _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans
open _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories
open _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors
variable (A : Type u) [CommRing A]
local instance jointCorrectionComponentModel : ModelCategory (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra := _root_.SerrePositivity.EInfinity.BarrattEccles.modelCategory A
local instance jointCorrectionComponentFactorization :
    (cofibrations (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra).HasFunctorialFactorization
      (trivialFibrations (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra) := ⟨⟨_root_.SerrePositivity.EInfinity.BarrattEccles.mappingCofibrantFactorization A⟩⟩

/-- 元の全補正同型の同じ成分の左右射影と、元の二頂点の辺は合成等式を満たす。 -/
theorem strictBETotJointSourceCorrection_component_composition
    (t : _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.StrictBETotJointSourceElements A) :
    let a := (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceCorrectedPairing A).app (Opposite.op ⦋0⦌) (nerveVertex t)
    let b := (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceNativePairing A).app (Opposite.op ⦋0⦌) (nerveVertex t)
    let f := ((_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceCorrectedPairingIso A).app (nerveVertex t)).hom
    ((homotopyOppositeEquivalence (_root_.SerrePositivity.EInfinity.BarrattEccles.CAlg_R A)).functor.map
      ((SSet.mapHomotopyCategory (edgewiseLeft (_root_.SerrePositivity.EInfinity.BarrattEccles.CAlg_R A))).map f)).unop ≫
        HomotopyCategory.homMk (twistedArrowVertexEdge a) ≫
          (SSet.mapHomotopyCategory (edgewiseRight (_root_.SerrePositivity.EInfinity.BarrattEccles.CAlg_R A))).map f =
            HomotopyCategory.homMk (twistedArrowVertexEdge b) := by
  dsimp only
  exact twistedArrowHom_composition _

end SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot
