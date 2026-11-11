module
public import SerrePositivity.KST.SConstruction.TracedBFCompositionRecoveryCylinder
public import SerrePositivity.KST.SConstruction.TracedBFTripleWhiskers
public import SerrePositivity.KST.SConstruction.EnrichedWhiskerHomotopies

/-! # 固定最終射との合成を保つ元の BF 比較の回収
概要：元の BF 比較の回収円柱と全高次比較を、固定した最終射との同じ豊穣合成で写す。
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
local instance tracedSecondWhiskerRecoverySpectrumSimplicialCategory :
    SimplicialCategory OmegaSpectrum.{u} := OmegaSpectrum.simplicialCategory
variable {I : Type u} [SmallCategory I] (F : I ⥤ StableModel.{u})
  {w x y z : I} (f : w ⟶ x) (g : x ⟶ y) (h : y ⟶ z)

/-- 元の BF 比較辺を固定最終射と実合成した同じ全辺。 -/
def monicKTracedNativeSecondWhisker :=
  enrichedComparisonRightWhisker
    (monicKTracedSpectrumMap F f) (monicKTracedSpectrumMap F g)
      (monicKTracedSpectrumMap F h) (monicKTracedSpectrumMap F (f ≫ g))
    (monicKTracedSpectrumCompositionEdge F f g)

/-- 元の BF 合成比較辺から保存した同じ合成面の復号辺への全端点固定回収円柱の像。 -/
def monicKTracedSecondWhiskerRecovery : SSet.Homotopy
    (SSet.yonedaEquiv.symm (monicKTracedNativeSecondWhisker F f g h).edge)
    (SSet.yonedaEquiv.symm (monicKTracedCoherentTripleSecondWhisker F f g h).edge) :=
  enrichedRightWhiskerHomotopy
    (monicKTracedSpectrumMap F f) (monicKTracedSpectrumMap F g)
      (monicKTracedSpectrumMap F h) (monicKTracedSpectrumMap F (f ≫ g))
    (monicKTracedCompositionRecoveryCylinder F f g)

/-- 合成後も元の全区間境界を全比較時刻で厳密に固定する。 -/
lemma monicKTracedSecondWhiskerRecovery_relative :
    ((SSet.boundary 1).ι ▷ (Δ[1] : SSet.{u})) ≫
        (monicKTracedSecondWhiskerRecovery F f g h).h =
      fst (SSet.boundary 1).toSSet Δ[1] ≫ (SSet.boundary 1).ι ≫
        SSet.yonedaEquiv.symm (monicKTracedNativeSecondWhisker F f g h).edge :=
  enrichedRightWhiskerHomotopy_relative _ _ _ _ _
    (monicKTracedCompositionRecoveryCylinder_relative F f g)

/-- 元の全高次回収比較を固定最終射との同じ実合成で写す。 -/
def monicKTracedSecondWhiskerRecoveryRealization :=
  monicKTracedCompositionRecoveryCylinderRealization F f g ≫
    enrichedFixedRightComposition (monicKTracedSpectrumMap F h)

/-- 元の全高次比較も、全パラメータで元の区間境界を厳密に固定する。 -/
lemma monicKTracedSecondWhiskerRecoveryRealization_relative :
    ((SSet.boundary 1).ι ▷ (Δ[2] : SSet.{u})) ≫
        monicKTracedSecondWhiskerRecoveryRealization F f g h =
      fst (SSet.boundary 1).toSSet Δ[2] ≫ (SSet.boundary 1).ι ≫
        SSet.yonedaEquiv.symm (monicKTracedNativeSecondWhisker F f g h).edge := by
  exact (fixedBoundaryFamily_postcomp _ _ (monicKTracedCompositionRecoveryCylinderRealization F f g)
    (monicKTracedCompositionRecoveryCylinderRealization_relative F f g)
    (enrichedFixedRightComposition (monicKTracedSpectrumMap F h))).trans
      (congrArg (fun q => fst (SSet.boundary 1).toSSet Δ[2] ≫ (SSet.boundary 1).ι ≫ q)
        (enrichedComparisonRightWhisker_map
          (monicKTracedSpectrumMap F f) (monicKTracedSpectrumMap F g)
            (monicKTracedSpectrumMap F h) (monicKTracedSpectrumMap F (f ≫ g))
          (monicKTracedSpectrumCompositionEdge F f g)).symm)

/-- 比較面は元の回収円柱の同じ全実合成像。 -/
lemma monicKTracedSecondWhiskerRecoveryRealization_comparison :
    ((Δ[1] : SSet.{u}) ◁ stdSimplex.δ 2) ≫
        monicKTracedSecondWhiskerRecoveryRealization F f g h =
      (monicKTracedSecondWhiskerRecovery F f g h).h := by
  change _ ≫ (monicKTracedCompositionRecoveryCylinderRealization F f g) ≫
    (enrichedFixedRightComposition (monicKTracedSpectrumMap F h)) = _
  rw [← Category.assoc, monicKTracedCompositionRecoveryCylinderRealization_comparison]
  exact (enrichedRightWhiskerHomotopy_h _ _ _ _ _).symm

/-- 元の第一回収円柱全体を、同じ高次比較の指定面の全像として保持する。 -/
lemma monicKTracedSecondWhiskerRecoveryRealization_first :
    ((Δ[1] : SSet.{u}) ◁ stdSimplex.δ 1) ≫
        monicKTracedSecondWhiskerRecoveryRealization F f g h =
      (endpointFixedTriangleHomotopy (monicKTracedCompositionRecovery F f g).first).h ≫
        enrichedFixedRightComposition (monicKTracedSpectrumMap F h) := by
  simpa only [monicKTracedSecondWhiskerRecoveryRealization, Category.assoc] using
    congrArg (· ≫ enrichedFixedRightComposition (monicKTracedSpectrumMap F h))
    (monicKTracedCompositionRecoveryCylinderRealization_first F f g)

/-- 元の第一実三角形全体も、同じ高次比較の指定面の全像として厳密に保持する。 -/
lemma monicKTracedSecondWhiskerRecoveryRealization_first_triangle :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.lower ≫ ((Δ[1] : SSet.{u}) ◁ stdSimplex.δ 1) ≫
        monicKTracedSecondWhiskerRecoveryRealization F f g h =
      SSet.yonedaEquiv.symm (monicKTracedCompositionRecovery F f g).first.simplex ≫
        enrichedFixedRightComposition (monicKTracedSpectrumMap F h) := by
  simpa only [monicKTracedSecondWhiskerRecoveryRealization, Category.assoc] using
    congrArg (· ≫ enrichedFixedRightComposition (monicKTracedSpectrumMap F h))
    (monicKTracedCompositionRecoveryCylinderRealization_first_triangle F f g)

/-- 元の第二回収円柱全体を、同じ高次比較の指定面の全像として保持する。 -/
lemma monicKTracedSecondWhiskerRecoveryRealization_second :
    ((Δ[1] : SSet.{u}) ◁ stdSimplex.δ 0) ≫
        monicKTracedSecondWhiskerRecoveryRealization F f g h =
      (endpointFixedTriangleHomotopy (monicKTracedCompositionRecovery F f g).second).h ≫
        enrichedFixedRightComposition (monicKTracedSpectrumMap F h) := by
  simpa only [monicKTracedSecondWhiskerRecoveryRealization, Category.assoc] using
    congrArg (· ≫ enrichedFixedRightComposition (monicKTracedSpectrumMap F h))
    (monicKTracedCompositionRecoveryCylinderRealization_second F f g)

/-- 元の第二実三角形全体も、同じ高次比較の指定面の全像として厳密に保持する。 -/
lemma monicKTracedSecondWhiskerRecoveryRealization_second_triangle :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.lower ≫ ((Δ[1] : SSet.{u}) ◁ stdSimplex.δ 0) ≫
        monicKTracedSecondWhiskerRecoveryRealization F f g h =
      SSet.yonedaEquiv.symm (monicKTracedCompositionRecovery F f g).second.simplex ≫
        enrichedFixedRightComposition (monicKTracedSpectrumMap F h) := by
  simpa only [monicKTracedSecondWhiskerRecoveryRealization, Category.assoc] using
    congrArg (· ≫ enrichedFixedRightComposition (monicKTracedSpectrumMap F h))
    (monicKTracedCompositionRecoveryCylinderRealization_second_triangle F f g)

end SerrePositivity.KST.SConstruction
