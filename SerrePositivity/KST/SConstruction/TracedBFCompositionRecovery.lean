module
public import SerrePositivity.KST.SConstruction.EnrichedReplacementComparisonDiamond
public import SerrePositivity.KST.SConstruction.TracedBFCoherentComposition

/-! # 元の BF 比較辺と保存した合成面の復号辺の実比較
概要：元の BF 比較辺と保存した同じ合成三角形の全復号辺を、共通辺へ結ぶ実三角形対にする。
方針：元の指定比較面・標準面・恒等面を保持する同じ比較四面体の全 Path 作用を使う。
規約：元の比較辺も保存した全二単体も選び直さない。両実比較面の全像を回収する。
使われ方：三入力の生成面と指定面の比較を元の BF 比較と raw 高次 prism へ接続する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet Spectra
open scoped Simplicial
local instance tracedCompositionRecoverySpectrumSimplicialCategory :
    SimplicialCategory OmegaSpectrum.{u} := OmegaSpectrum.simplicialCategory
variable {I : Type u} [SmallCategory I] (F : I ⥤ StableModel.{u})
  {x y z : I} (f : x ⟶ y) (g : y ⟶ z)

/-- 元の BF 比較辺と保存した合成面の全復号辺を結ぶ、同じ元の実三角形対の保存データ。 -/
def monicKTracedCompositionRecoveryData :=
  enrichedReplacementComparisonData (monicKTracedSpectrumMap F f) (monicKTracedSpectrumMap F g)
    (monicKTracedSpectrumMap F (f ≫ g)) (monicKTracedSpectrumCompositionEdge F f g)
    (monicKTracedCoherentCompositionData F f g)

/-- 同じ BF 写像空間において元の比較辺・復号辺を共通辺へ結ぶ同じ実三角形対。 -/
def monicKTracedCompositionRecovery := (monicKTracedCompositionRecoveryData F f g).val

/-- 第一実比較三角形は、指定比較面を保持する元の比較四面体の第一全 Path 二単体の像。 -/
lemma monicKTracedCompositionRecovery_first_image :
    (monicKTracedCompositionRecovery F f g).first.simplex =
      (eqToHom (enrichedReplacementMappingSpace_eq (monicKTracedSpectrumMap F f)
        (monicKTracedSpectrumMap F g) (monicKTracedSpectrumMap F (f ≫ g))
        (monicKTracedSpectrumCompositionEdge F f g)
        (monicKTracedCoherentCompositionData F f g))).app (Opposite.op ⦋2⦌)
        (coherentSimplexFirstInsertionTriangle
          (monicKTracedCoherentCompositionData F f g).simplex 0 1 2 3
          (by decide) (by decide) (by decide)).simplex :=
  enrichedReplacementComparison_first_image _ _ _ _ _

/-- 第二実比較三角形も、保存した元の合成面を持つ同じ四面体の第二全 Path 二単体の像。 -/
lemma monicKTracedCompositionRecovery_second_image :
    (monicKTracedCompositionRecovery F f g).second.simplex =
      (eqToHom (enrichedReplacementMappingSpace_eq (monicKTracedSpectrumMap F f)
        (monicKTracedSpectrumMap F g) (monicKTracedSpectrumMap F (f ≫ g))
        (monicKTracedSpectrumCompositionEdge F f g)
        (monicKTracedCoherentCompositionData F f g))).app (Opposite.op ⦋2⦌)
        (coherentSimplexSecondInsertionTriangle
          (monicKTracedCoherentCompositionData F f g).simplex 0 1 2 3
          (by decide) (by decide) (by decide)).simplex :=
  enrichedReplacementComparison_second_image _ _ _ _ _

end SerrePositivity.KST.SConstruction
