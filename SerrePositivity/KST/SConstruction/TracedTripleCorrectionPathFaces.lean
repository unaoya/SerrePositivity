module
public import SerrePositivity.KST.SConstruction.TracedTripleBinaryImages

/-! # 左右三本補正辺路の元の全共通辺
概要：元の前後二射の二部分三角形の全辺を、同じ三本の補正辺と実交換面へ同定する。
方針：元の raw 段射の関手法則、BF 段射の前合成の結合則・後合成との交換を使う。
規約：全辺の実写像を厳密に同定し、成分や合成類だけの一致にはしない。
使われ方：元の全段三角形・二部分三角形・交換面の四面貼り合わせ。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet Spectra
open scoped Simplicial
local instance correctionPathSpectrumSimplicialCategory :
    SimplicialCategory OmegaSpectrum.{u} := OmegaSpectrum.simplicialCategory
variable {I : Type u} [SmallCategory I] (F : I ⥤ StableModel.{u})
  {w x y z : I} (f : w ⟶ x) (g : x ⟶ y) (h : y ⟶ z)

/-- 前二射二部分三角形の第一全辺は、右外側二部分三角形の同じ第一全辺。 -/
lemma monicKTracedTripleCorrectionPath_first (n : ℕ) :
    stdSimplex.δ 2 ≫
        SSet.yonedaEquiv.symm (monicKTracedTripleFirstPairBinaryTriangle F f g h n).simplex =
      stdSimplex.δ 2 ≫
        SSet.yonedaEquiv.symm (monicKPrismCompositeBinaryPointTriangle F f (g ≫ h) n).simplex := by
  rw [monicKTracedTripleFirstPairBinaryTriangle_realization, ← Category.assoc,
    monicKPrismCompositeBinaryPointTriangle_first, monicKPrismCompositeBinaryPointTriangle_first,
    Category.assoc, monicKTracedTripleRawPost_comp]

/-- 前二射・後二射二部分三角形の中間全辺は、同じ前後合成を辿る全実写像。 -/
lemma monicKTracedTripleCorrectionPath_middle (n : ℕ) :
    stdSimplex.δ 0 ≫
        SSet.yonedaEquiv.symm (monicKTracedTripleFirstPairBinaryTriangle F f g h n).simplex =
      stdSimplex.δ 2 ≫
        SSet.yonedaEquiv.symm (monicKTracedTripleLastPairBinaryTriangle F f g h n).simplex := by
  rw [monicKTracedTripleFirstPairBinaryTriangle_realization,
    monicKTracedTripleLastPairBinaryTriangle_realization]
  simp only [← Category.assoc]
  rw [monicKPrismCompositeBinaryPointTriangle_second, monicKPrismCompositeBinaryPointTriangle_first]
  simp only [Category.assoc]
  rw [monicKTracedTripleLastPairStageMap_post]

/-- 後二射二部分三角形の最後の全辺は、元の実交換三角形対の同じ第二上辺。 -/
lemma monicKTracedTripleCorrectionPath_last (n : ℕ) :
    stdSimplex.δ 0 ≫
        SSet.yonedaEquiv.symm (monicKTracedTripleLastPairBinaryTriangle F f g h n).simplex =
      SSet.yonedaEquiv.symm (monicKTracedTripleInterchangeSecondUpper F f g h n).edge := by
  rw [monicKTracedTripleLastPairBinaryTriangle_realization, ← Category.assoc,
    monicKPrismCompositeBinaryPointTriangle_second]
  calc
    _ = monicKTracedUnaryCorrectionAtPoint F h n ≫
        (monicKTracedTripleLastPairStageMap F g z n ≫
          monicKTracedTripleLastPairStageMap F f z n) := Category.assoc _ _ _
    _ = _ := (congrArg (monicKTracedUnaryCorrectionAtPoint F h n ≫ ·)
      (monicKTracedTripleLastPairStageMap_comp (z := z) F f g n)).trans
        ((pointedFixedLeftVertexComposition_apply
          ((OmegaSpectrum.evaluation (kOmegaSpectrum (F.obj w)) (kOmegaSpectrum (F.obj y)) n).app
            (Opposite.op ⦋0⦌) (SimplicialCategory.homEquiv' _ _
              (monicKTracedSpectrumMap F f ≫ monicKTracedSpectrumMap F g)))
          (monicKTracedUnaryCorrectionAtPoint F h n)).trans
            (monicKTracedTripleInterchangeSecondUpper_map F f g h n).symm)

end SerrePositivity.KST.SConstruction
