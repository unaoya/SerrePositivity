module
public import SerrePositivity.KST.SConstruction.TracedTripleStageCompositionLaws

/-! # 前後二射の元の全二部分三角形を同じ三入力空間へ写す
概要：前二射・後二射の二部分三角形の全像を、元の固定段射の合成で保持する。
方針：元の全実三角形を同じ全 Hom 写像で写し、元の段三角形と共有する対角面を回収する。
規約：両全二単体を保持し、辺の合成類だけに移さない。
使われ方：左右の三本補正辺路の厳密な照合と元の四面の貼り合わせ。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet Spectra
open scoped Simplicial
variable {I : Type u} [SmallCategory I] (F : I ⥤ StableModel.{u})
  {w x y z : I} (f : w ⟶ x) (g : x ⟶ y) (h : y ⟶ z)

/-- 元の前二射の全二部分三角形の、元の最終段射による同じ後合成像。 -/
def monicKTracedTripleFirstPairBinaryTriangle (n : ℕ) :=
  (monicKPrismCompositeBinaryPointTriangle F f g n).map
    (PointedObject.basedHomMap ((kOmegaSpectrum (F.obj w)).level n).space
      (kKanSequenceLevelMap (F.map h) n)).right

/-- 元の後二射の全二部分三角形の、元の第一 BF 段射との同じ合成像。 -/
def monicKTracedTripleLastPairBinaryTriangle (n : ℕ) :=
  (monicKPrismCompositeBinaryPointTriangle F g h n).map
    (monicKTracedTripleLastPairStageMap F f z n)

/-- 前二射の全二単体は、元の同じ全二部分三角形の後合成像そのもの。 -/
lemma monicKTracedTripleFirstPairBinaryTriangle_realization (n : ℕ) :
    SSet.yonedaEquiv.symm (monicKTracedTripleFirstPairBinaryTriangle F f g h n).simplex =
      SSet.yonedaEquiv.symm (monicKPrismCompositeBinaryPointTriangle F f g n).simplex ≫
        (PointedObject.basedHomMap ((kOmegaSpectrum (F.obj w)).level n).space
          (kKanSequenceLevelMap (F.map h) n)).right :=
  (SSet.yonedaEquiv_symm_comp (monicKPrismCompositeBinaryPointTriangle F f g n).simplex
    (PointedObject.basedHomMap ((kOmegaSpectrum (F.obj w)).level n).space
      (kKanSequenceLevelMap (F.map h) n)).right).symm

/-- 後二射の全二単体も、元の同じ全二部分三角形の実合成像そのもの。 -/
lemma monicKTracedTripleLastPairBinaryTriangle_realization (n : ℕ) :
    SSet.yonedaEquiv.symm (monicKTracedTripleLastPairBinaryTriangle F f g h n).simplex =
      SSet.yonedaEquiv.symm (monicKPrismCompositeBinaryPointTriangle F g h n).simplex ≫
        monicKTracedTripleLastPairStageMap F f z n :=
  (SSet.yonedaEquiv_symm_comp (monicKPrismCompositeBinaryPointTriangle F g h n).simplex
    (monicKTracedTripleLastPairStageMap F f z n)).symm

/-- 前二射の同じ対角面全体は、元の前二射段三角形の同じ合成補正辺。 -/
lemma monicKTracedTripleFirstPairBinaryTriangle_direct (n : ℕ) :
    stdSimplex.δ 1 ≫
        SSet.yonedaEquiv.symm (monicKTracedTripleFirstPairBinaryTriangle F f g h n).simplex =
      stdSimplex.δ 1 ≫
        SSet.yonedaEquiv.symm (monicKTracedTripleFirstPairStageTriangle F f g h n).simplex := by
  rw [monicKTracedTripleFirstPairBinaryTriangle_realization, ← Category.assoc,
    monicKPrismCompositeBinaryPointTriangle_direct, monicKTracedTripleFirstPairStageTriangle_direct]

/-- 後二射の同じ対角面全体も、元の後二射段三角形の同じ合成補正辺。 -/
lemma monicKTracedTripleLastPairBinaryTriangle_direct (n : ℕ) :
    stdSimplex.δ 1 ≫
        SSet.yonedaEquiv.symm (monicKTracedTripleLastPairBinaryTriangle F f g h n).simplex =
      stdSimplex.δ 1 ≫
        SSet.yonedaEquiv.symm (monicKTracedTripleLastPairStageTriangle F f g h n).simplex := by
  rw [monicKTracedTripleLastPairBinaryTriangle_realization, ← Category.assoc,
    monicKPrismCompositeBinaryPointTriangle_direct, monicKTracedTripleLastPairStageTriangle_direct]

end SerrePositivity.KST.SConstruction
