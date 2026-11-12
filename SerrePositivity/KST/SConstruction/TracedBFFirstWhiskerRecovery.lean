module
public import SerrePositivity.KST.SConstruction.TracedBFCompositionRecoveryCylinder
public import SerrePositivity.KST.SConstruction.TracedBFTripleWhiskers
public import SerrePositivity.KST.SConstruction.EnrichedWhiskerHomotopies

/-! # 固定第一射との合成を保つ元の BF 比較の回収
概要：元の BF 比較の回収円柱と全高次比較を、固定した第一射との同じ豊穣合成で写す。
方針：全 Hom の合成写像で元の全円柱を後合成し、元の全区間境界と指定面を回収する。
規約：比較円柱や元の二単体を選び直さず、全高次比較の実像を保持する。
使われ方：三入力の二実三角形の辺を元の BF 比較辺の合成へ相対的に移す。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet Spectra
open scoped Simplicial
local instance tracedFirstWhiskerRecoverySpectrumSimplicialCategory :
    SimplicialCategory OmegaSpectrum.{u} := OmegaSpectrum.simplicialCategory
variable {I : Type u} [SmallCategory I] (F : I ⥤ StableModel.{u})
  {w x y z : I} (f : w ⟶ x) (g : x ⟶ y) (h : y ⟶ z)

/-- 元の BF 比較辺を固定第一射と実合成した同じ全辺。 -/
def monicKTracedNativeFirstWhisker :=
  enrichedComparisonLeftWhisker
    (monicKTracedSpectrumMap F f) (monicKTracedSpectrumMap F g)
      (monicKTracedSpectrumMap F h) (monicKTracedSpectrumMap F (g ≫ h))
    (monicKTracedSpectrumCompositionEdge F g h)

/-- 元の BF 合成比較辺から保存した同じ合成面の復号辺への全端点固定回収円柱の像。 -/
def monicKTracedFirstWhiskerRecovery : SSet.Homotopy
    (SSet.yonedaEquiv.symm (monicKTracedNativeFirstWhisker F f g h).edge)
    (SSet.yonedaEquiv.symm (monicKTracedCoherentTripleFirstWhisker F f g h).edge) :=
  enrichedLeftWhiskerHomotopy
    (monicKTracedSpectrumMap F f) (monicKTracedSpectrumMap F g)
      (monicKTracedSpectrumMap F h) (monicKTracedSpectrumMap F (g ≫ h))
    (monicKTracedCompositionRecoveryCylinder F g h)

/-- 合成後も元の全区間境界を全比較時刻で厳密に固定する。 -/
lemma monicKTracedFirstWhiskerRecovery_relative :
    ((SSet.boundary 1).ι ▷ (Δ[1] : SSet.{u})) ≫
        (monicKTracedFirstWhiskerRecovery F f g h).h =
      fst (SSet.boundary 1).toSSet Δ[1] ≫ (SSet.boundary 1).ι ≫
        SSet.yonedaEquiv.symm (monicKTracedNativeFirstWhisker F f g h).edge :=
  enrichedLeftWhiskerHomotopy_relative _ _ _ _ _
    (monicKTracedCompositionRecoveryCylinder_relative F g h)

/-- 元の全高次回収比較を固定第一射との同じ実合成で写す。 -/
def monicKTracedFirstWhiskerRecoveryRealization :=
  monicKTracedCompositionRecoveryCylinderRealization F g h ≫
    enrichedFixedLeftComposition (monicKTracedSpectrumMap F f)

/-- 元の全高次比較も、全パラメータで元の区間境界を厳密に固定する。 -/
lemma monicKTracedFirstWhiskerRecoveryRealization_relative :
    ((SSet.boundary 1).ι ▷ (Δ[2] : SSet.{u})) ≫
        monicKTracedFirstWhiskerRecoveryRealization F f g h =
      fst (SSet.boundary 1).toSSet Δ[2] ≫ (SSet.boundary 1).ι ≫
        SSet.yonedaEquiv.symm (monicKTracedNativeFirstWhisker F f g h).edge := by
  exact (fixedBoundaryFamily_postcomp _ _ (monicKTracedCompositionRecoveryCylinderRealization F g h)
    (monicKTracedCompositionRecoveryCylinderRealization_relative F g h)
    (enrichedFixedLeftComposition (monicKTracedSpectrumMap F f))).trans
      (congrArg (fun q => fst (SSet.boundary 1).toSSet Δ[2] ≫ (SSet.boundary 1).ι ≫ q)
        (enrichedComparisonLeftWhisker_map
          (monicKTracedSpectrumMap F f) (monicKTracedSpectrumMap F g)
            (monicKTracedSpectrumMap F h) (monicKTracedSpectrumMap F (g ≫ h))
          (monicKTracedSpectrumCompositionEdge F g h)).symm)

/-- 比較面は元の回収円柱の同じ全実合成像。 -/
lemma monicKTracedFirstWhiskerRecoveryRealization_comparison :
    ((Δ[1] : SSet.{u}) ◁ stdSimplex.δ 2) ≫
        monicKTracedFirstWhiskerRecoveryRealization F f g h =
      (monicKTracedFirstWhiskerRecovery F f g h).h := by
  change _ ≫ (monicKTracedCompositionRecoveryCylinderRealization F g h) ≫
    (enrichedFixedLeftComposition (monicKTracedSpectrumMap F f)) = _
  rw [← Category.assoc, monicKTracedCompositionRecoveryCylinderRealization_comparison]
  exact (enrichedLeftWhiskerHomotopy_h _ _ _ _ _).symm

/-- 元の第一回収円柱全体を、同じ高次比較の指定面の全像として保持する。 -/
lemma monicKTracedFirstWhiskerRecoveryRealization_first :
    ((Δ[1] : SSet.{u}) ◁ stdSimplex.δ 1) ≫
        monicKTracedFirstWhiskerRecoveryRealization F f g h =
      (endpointFixedTriangleHomotopy (monicKTracedCompositionRecovery F g h).first).h ≫
        enrichedFixedLeftComposition (monicKTracedSpectrumMap F f) := by
  simpa only [monicKTracedFirstWhiskerRecoveryRealization, Category.assoc] using
    congrArg (· ≫ enrichedFixedLeftComposition (monicKTracedSpectrumMap F f))
    (monicKTracedCompositionRecoveryCylinderRealization_first F g h)

/-- 元の第一実三角形全体も、同じ高次比較の指定面の全像として厳密に保持する。 -/
lemma monicKTracedFirstWhiskerRecoveryRealization_first_triangle :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.lower ≫ ((Δ[1] : SSet.{u}) ◁ stdSimplex.δ 1) ≫
        monicKTracedFirstWhiskerRecoveryRealization F f g h =
      SSet.yonedaEquiv.symm (monicKTracedCompositionRecovery F g h).first.simplex ≫
        enrichedFixedLeftComposition (monicKTracedSpectrumMap F f) := by
  simpa only [monicKTracedFirstWhiskerRecoveryRealization, Category.assoc] using
    congrArg (· ≫ enrichedFixedLeftComposition (monicKTracedSpectrumMap F f))
    (monicKTracedCompositionRecoveryCylinderRealization_first_triangle F g h)

/-- 元の第二回収円柱全体を、同じ高次比較の指定面の全像として保持する。 -/
lemma monicKTracedFirstWhiskerRecoveryRealization_second :
    ((Δ[1] : SSet.{u}) ◁ stdSimplex.δ 0) ≫
        monicKTracedFirstWhiskerRecoveryRealization F f g h =
      (endpointFixedTriangleHomotopy (monicKTracedCompositionRecovery F g h).second).h ≫
        enrichedFixedLeftComposition (monicKTracedSpectrumMap F f) := by
  simpa only [monicKTracedFirstWhiskerRecoveryRealization, Category.assoc] using
    congrArg (· ≫ enrichedFixedLeftComposition (monicKTracedSpectrumMap F f))
    (monicKTracedCompositionRecoveryCylinderRealization_second F g h)

/-- 元の第二実三角形全体も、同じ高次比較の指定面の全像として厳密に保持する。 -/
lemma monicKTracedFirstWhiskerRecoveryRealization_second_triangle :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.lower ≫ ((Δ[1] : SSet.{u}) ◁ stdSimplex.δ 0) ≫
        monicKTracedFirstWhiskerRecoveryRealization F f g h =
      SSet.yonedaEquiv.symm (monicKTracedCompositionRecovery F g h).second.simplex ≫
        enrichedFixedLeftComposition (monicKTracedSpectrumMap F f) := by
  simpa only [monicKTracedFirstWhiskerRecoveryRealization, Category.assoc] using
    congrArg (· ≫ enrichedFixedLeftComposition (monicKTracedSpectrumMap F f))
    (monicKTracedCompositionRecoveryCylinderRealization_second_triangle F g h)

end SerrePositivity.KST.SConstruction
