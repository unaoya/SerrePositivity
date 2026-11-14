module
public import SerrePositivity.KST.SConstruction.TracedBFTripleComparisonDiamond
public import SerrePositivity.KST.SConstruction.EnrichedComparisonWhiskers
public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.Subdivision.TriangleDiamondComposition

/-! # 三入力 BF 二経路の元の固定因子との実比較辺
概要：元の保存面の比較辺を元の第一射・最終射と合成し、同じ BF 写像空間の実辺にする。
方針：豊穣合成の元の全一単体を保持し、三射合成の両括弧を通常の圏の等号で合わせる。
規約：既存の比較辺を選び直さない。元の二単体全体は四辺の表示変更でも保持する。
使われ方：三入力の元の BF 二経路を、共通対角辺を持つ実合成三角形へ束ねる。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet Spectra
open scoped Simplicial
local instance tracedTripleWhiskerSpectrumSimplicialCategory :
    SimplicialCategory OmegaSpectrum.{u} := OmegaSpectrum.simplicialCategory
variable {I : Type u} [SmallCategory I] (F : I ⥤ StableModel.{u})
  {w x y z : I} (f : w ⟶ x) (g : x ⟶ y) (h : y ⟶ z)

/-- 元の後二射の比較辺を元の第一射と合成した、同じ BF 写像空間の実辺。 -/
def monicKTracedCoherentTripleFirstWhisker :=
  enrichedComparisonLeftWhisker (monicKTracedSpectrumMap F f) (monicKTracedSpectrumMap F g)
    (monicKTracedSpectrumMap F h) (monicKTracedSpectrumMap F (g ≫ h))
    (coherentTriangleMappingEdge (monicKTracedSpectrumMap F g) (monicKTracedSpectrumMap F h)
      (monicKTracedSpectrumMap F (g ≫ h)) (monicKTracedCoherentComposition F g h))

/-- 元の前二射の比較辺を元の最終射と合成した、同じ BF 写像空間の実辺。 -/
def monicKTracedCoherentTripleSecondWhisker :=
  enrichedComparisonRightWhisker (monicKTracedSpectrumMap F f) (monicKTracedSpectrumMap F g)
    (monicKTracedSpectrumMap F h) (monicKTracedSpectrumMap F (f ≫ g))
    (coherentTriangleMappingEdge (monicKTracedSpectrumMap F f) (monicKTracedSpectrumMap F g)
      (monicKTracedSpectrumMap F (f ≫ g)) (monicKTracedCoherentComposition F f g))

/-- 元の全二単体を保ち、四辺を同じ実 BF 比較辺の表示へ合わせた二単体対。 -/
def monicKTracedCoherentTripleEdgeDiamond :=
  (monicKTracedCoherentTripleDiamond F f g h).ofEq rfl rfl
    (enrichedComparisonLeftWhisker_edge (monicKTracedSpectrumMap F f)
      (monicKTracedSpectrumMap F g) (monicKTracedSpectrumMap F h)
      (monicKTracedSpectrumMap F (g ≫ h))
      (coherentTriangleMappingEdge (monicKTracedSpectrumMap F g) (monicKTracedSpectrumMap F h)
        (monicKTracedSpectrumMap F (g ≫ h)) (monicKTracedCoherentComposition F g h))).symm
    (enrichedComparisonRightWhisker_edge (monicKTracedSpectrumMap F f)
      (monicKTracedSpectrumMap F g) (monicKTracedSpectrumMap F h)
      (monicKTracedSpectrumMap F (f ≫ g))
      (coherentTriangleMappingEdge (monicKTracedSpectrumMap F f) (monicKTracedSpectrumMap F g)
        (monicKTracedSpectrumMap F (f ≫ g)) (monicKTracedCoherentComposition F f g))).symm

end SerrePositivity.KST.SConstruction
