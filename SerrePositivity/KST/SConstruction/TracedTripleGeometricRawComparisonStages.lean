module
public import SerrePositivity.KST.SConstruction.TracedTripleGeometricStageComparison
public import SerrePositivity.KST.SConstruction.TracedTripleRawComparisonStages

/-! # 元の零段を保つ実六対角面消去の raw 全段比較族
概要：零段には元の同じ全比較を使い、正の段を実四面体の消去から構成する。
方針：段数で場合分けし、元の両 BF 辺の全 raw 評価の表示だけを合わせる。
規約：元の零段円柱と全高次零段比較を保持する。隣接段適合は別工程。
使われ方：全高次 prism と消去選択を同時に保つ相対逐次構成の実入力族。
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

/-- 元の零段円柱と、正の段の実六対角面消去の全円柱を保持する同じ全段族。 -/
def monicKTracedTripleGeometricRawComparisonStages (n : ℕ) :
    MonicKTracedTripleRawStageComparison F f g h n :=
  match n with
  | 0 => monicKTracedTripleRawZeroComparison F f g h
  | n + 1 => monicKTracedTripleGeometricRawStageComparison F f g h (n + 1)

/-- 零段には元の同じ全端点固定比較円柱を厳密に使う。 -/
lemma monicKTracedTripleGeometricRawComparisonStages_zero :
    monicKTracedTripleGeometricRawComparisonStages F f g h 0 =
      monicKTracedTripleRawZeroComparison F f g h := rfl

/-- 正の段は、元の全実消去からの同じ全比較円柱を厳密に保持する。 -/
lemma monicKTracedTripleGeometricRawComparisonStages_succ (n : ℕ) :
    (monicKTracedTripleGeometricRawComparisonStages F f g h (n + 1)).homotopy.h =
      (monicKTracedTripleGeometricRawStageComparison F f g h (n + 1)).homotopy.h := rfl

/-- 元の全高次零段比較の同じ指定面は、同じ全零段円柱そのもの。 -/
lemma monicKTracedTripleGeometricRawComparisonStages_zero_realization :
    ((Δ[1] : SSet.{u}) ◁ stdSimplex.δ 2) ≫
        monicKTracedTripleZeroComparisonRealization F f g h =
      (monicKTracedTripleGeometricRawComparisonStages F f g h 0).homotopy.h :=
  monicKTracedTripleRawZeroComparison_realization F f g h

/-- 全段の同じ全円柱は、元の全入力境界を全比較時刻で厳密に固定する。 -/
lemma monicKTracedTripleGeometricRawComparisonStages_relative (n : ℕ) :
    ((SSet.boundary 1).ι ▷ (Δ[1] : SSet.{u})) ≫
        (monicKTracedTripleGeometricRawComparisonStages F f g h n).homotopy.h =
      fst (∂Δ[1] : SSet.{u}) Δ[1] ≫ (SSet.boundary 1).ι ≫
        SSet.yonedaEquiv.symm
          ((((monicKTracedNativeTriplePrescribedEdge F f g h).map
            (kRawMappingProjection (F.obj w) (F.obj z))).map
              (RawSpectrumMapping.evaluation
                (kOmegaSpectrum (F.obj w)) (kKanSequence (F.obj z)) n)).edge) :=
  (monicKTracedTripleGeometricRawComparisonStages F f g h n).relative

end SerrePositivity.KST.SConstruction
