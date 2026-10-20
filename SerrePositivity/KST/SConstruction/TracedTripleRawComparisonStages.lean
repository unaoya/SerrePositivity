module
public import SerrePositivity.KST.SConstruction.TracedTripleRawStageComparison
public import SerrePositivity.KST.SConstruction.TracedBFTripleZeroComparison

/-! # 元の零段円柱を厳密に保持する全 raw 段比較族
概要：零段には元の比較円柱をそのまま使い、正の段には十二面からの実比較を使う。
方針：段数で場合分けし、写像の二回作用と合成作用の表示だけを合わせる。
規約：各段の全端点固定族であり、隣接段の構造適合はまだ主張しない。
使われ方：零段を変更しない相対逐次構成の入力族。
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

/-- 元の raw 射影の各段を両端に持つ全端点固定比較の型。 -/
abbrev MonicKTracedTripleRawStageComparison (n : ℕ) := EndpointFixedEdgeCylinder
    (((monicKTracedNativeTriplePrescribedEdge F f g h).map
      (kRawMappingProjection (F.obj w) (F.obj z))).map
        (RawSpectrumMapping.evaluation (kOmegaSpectrum (F.obj w)) (kKanSequence (F.obj z)) n))
    (((monicKTracedCoherentTripleGeneratedEdge F f g h).map
      (kRawMappingProjection (F.obj w) (F.obj z))).map
        (RawSpectrumMapping.evaluation (kOmegaSpectrum (F.obj w)) (kKanSequence (F.obj z)) n))

/-- 元の全零段円柱を厳密に使う、同じ両 raw 辺の全段比較族。 -/
def monicKTracedTripleRawComparisonStages (n : ℕ) :
    MonicKTracedTripleRawStageComparison F f g h n :=
  match n with
  | 0 => monicKTracedTripleRawZeroComparison F f g h
  | n + 1 => monicKTracedTripleRawStageComparison F f g h (n + 1)

/-- 零段は元の端点固定比較円柱そのもの。 -/
lemma monicKTracedTripleRawComparisonStages_zero :
    monicKTracedTripleRawComparisonStages F f g h 0 =
      monicKTracedTripleRawZeroComparison F f g h := rfl

/-- 正の各段の全円柱は十二面から構成した元の同じ全円柱。 -/
lemma monicKTracedTripleRawComparisonStages_succ (n : ℕ) :
    (monicKTracedTripleRawComparisonStages F f g h (n + 1)).homotopy.h =
      (monicKTracedTripleRawStageComparison F f g h (n + 1)).homotopy.h := rfl

/-- 元の零段の全高次比較は、この族の同じ全零段円柱を指定面に厳密に保持する。 -/
lemma monicKTracedTripleRawComparisonStages_zero_realization :
    ((Δ[1] : SSet.{u}) ◁ stdSimplex.δ 2) ≫
        monicKTracedTripleZeroComparisonRealization F f g h =
      (monicKTracedTripleRawComparisonStages F f g h 0).homotopy.h :=
  monicKTracedTripleRawZeroComparison_realization F f g h

/-- 全段の比較は元の入力区間の全境界を全時刻で厳密に固定する。 -/
lemma monicKTracedTripleRawComparisonStages_relative (n : ℕ) :
    ((SSet.boundary 1).ι ▷ (Δ[1] : SSet.{u})) ≫
        (monicKTracedTripleRawComparisonStages F f g h n).homotopy.h =
      fst (SSet.boundary 1).toSSet Δ[1] ≫ (SSet.boundary 1).ι ≫
        SSet.yonedaEquiv.symm
          ((((monicKTracedNativeTriplePrescribedEdge F f g h).map
            (kRawMappingProjection (F.obj w) (F.obj z))).map
              (RawSpectrumMapping.evaluation
                (kOmegaSpectrum (F.obj w)) (kKanSequence (F.obj z)) n)).edge) :=
  (monicKTracedTripleRawComparisonStages F f g h n).relative

end SerrePositivity.KST.SConstruction
