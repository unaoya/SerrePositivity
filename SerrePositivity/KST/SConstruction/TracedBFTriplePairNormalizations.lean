module
public import SerrePositivity.KST.SConstruction.TracedBFTriplePairStageTriangles
public import SerrePositivity.KST.SConstruction.FixedBoundaryPostcomposition

/-! # 固定因子へ写した元の直接補正の全端点固定正規化
概要：前二射・後二射の元の補正辺の正規化を、同じ三入力 raw 写像空間へ写す。
方針：元の全正規化円柱を、段三角形と同じ固定因子合成で後合成する。
規約：元の全円柱と全区間境界の固定を保持し、新しい比較を選ばない。
使われ方：元の四面の貼り合わせで、共有する単一合成射の補正へ同じ全辺を合わせる。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet Spectra
open SerrePositivity.InfinityCategories
open scoped Simplicial
variable {I : Type u} [SmallCategory I] (F : I ⥤ StableModel.{u})
  {w x y z : I} (f : w ⟶ x) (g : x ⟶ y) (h : y ⟶ z)

/-- 前二射の同じ直接補正正規化を、元の最終段射で後合成した全円柱。 -/
def monicKTracedTripleFirstPairNormalization (n : ℕ) :=
  _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp (monicKTracedCompositionStageFirstNormalization F f g n)
    (PointedObject.basedHomMap ((kOmegaSpectrum (F.obj w)).level n).space
      (kKanSequenceLevelMap (F.map h) n)).right

/-- 元の全円柱そのものの同じ実後合成像を保持する。 -/
lemma monicKTracedTripleFirstPairNormalization_h (n : ℕ) :
    (monicKTracedTripleFirstPairNormalization F f g h n).h =
      (monicKTracedCompositionStageFirstNormalization F f g n).h ≫
        (PointedObject.basedHomMap ((kOmegaSpectrum (F.obj w)).level n).space
          (kKanSequenceLevelMap (F.map h) n)).right := rfl

/-- 前二射の同じ補正辺の全区間境界を、全比較時刻で厳密に固定する。 -/
lemma monicKTracedTripleFirstPairNormalization_relative (n : ℕ) :
    ((SSet.boundary 1).ι ▷ (Δ[1] : SSet.{u})) ≫
        (monicKTracedTripleFirstPairNormalization F f g h n).h =
      fst (∂Δ[1] : SSet.{u}) Δ[1] ≫ (SSet.boundary 1).ι ≫
        SSet.yonedaEquiv.symm (monicKTracedCompositionStageTriangleData F f g n).first.edge ≫
          (PointedObject.basedHomMap ((kOmegaSpectrum (F.obj w)).level n).space
            (kKanSequenceLevelMap (F.map h) n)).right :=
  fixedBoundaryHomotopy_postcomp _ _ _
    (monicKTracedCompositionStageFirstNormalization_relative F f g n) _

/-- 後二射の同じ直接補正正規化を、元の第一 BF 段射と合成した全円柱。 -/
def monicKTracedTripleLastPairNormalization (n : ℕ) :=
  _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp (monicKTracedCompositionStageFirstNormalization F g h n)
    (monicKTracedTripleLastPairStageMap F f z n)

/-- 後二射でも元の全円柱そのものの同じ実合成像を保持する。 -/
lemma monicKTracedTripleLastPairNormalization_h (n : ℕ) :
    (monicKTracedTripleLastPairNormalization F f g h n).h =
      (monicKTracedCompositionStageFirstNormalization F g h n).h ≫
        monicKTracedTripleLastPairStageMap F f z n := rfl

/-- 後二射の同じ補正辺の全区間境界も、全比較時刻で厳密に固定する。 -/
lemma monicKTracedTripleLastPairNormalization_relative (n : ℕ) :
    ((SSet.boundary 1).ι ▷ (Δ[1] : SSet.{u})) ≫
        (monicKTracedTripleLastPairNormalization F f g h n).h =
      fst (∂Δ[1] : SSet.{u}) Δ[1] ≫ (SSet.boundary 1).ι ≫
        SSet.yonedaEquiv.symm (monicKTracedCompositionStageTriangleData F g h n).first.edge ≫
          monicKTracedTripleLastPairStageMap F f z n :=
  fixedBoundaryHomotopy_postcomp _ _ _
    (monicKTracedCompositionStageFirstNormalization_relative F g h n) _

end SerrePositivity.KST.SConstruction
