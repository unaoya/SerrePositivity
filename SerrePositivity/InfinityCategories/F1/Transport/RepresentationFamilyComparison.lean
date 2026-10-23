module

public import SerrePositivity.InfinityCategories.F1.Transport.RepresentationMappingSpaceMap
public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.UnstraighteningSourceFamilyComparison
public import SerrePositivity.InfinityCategories.F1.FunctorCategories.RelativeFunctorPostUncurry

/-!
概要：一般の表現の族の復元と unstraightening の作用を前後合成で結ぶ。
方針：表現の比較射で pointed な始点と終点を表示し同じ prism を比較する。
規約：図式と全空間の両方で指定した比較射を使う。
使われ方：一般の straightening の写像空間比較の同値性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：相対射を実現する変換の unstraightening は元の相対射の前後合成と整合する。
方針：同じ prism の始点と終点を表現の比較射で書き直す。
規約：底の quasicategory 性を要求しない。
使われ方：全相対写像空間の普遍族の可換式。 -/
def transportRepresentationFamilyComparisonIso {E F B K : SSet.{u + 1}}
    {p : E ⟶ B} {q : F ⟶ B} [LeftFibration p] [LeftFibration q]
    (R : LeftTransportRepresentation p) (S : LeftTransportRepresentation q)
    (t : K ⟶ leftUnstraighteningTransformationSpace R.diagram S.diagram)
    (f : E ⊗ K ⟶ F) (hf : f ≫ q = fst E K ≫ p)
    (w : TransportRepresentationFamilyWitness R S t f) :
    FunctorIso ((t ≫ leftUnstraighteningMappingSpaceMap R.diagram S.diagram) ≫
      relativeFunctorOverPre (leftUnstraighteningProjection S.diagram)
        (Over.homMk (U := Over.mk p)
          (V := Over.mk (leftUnstraighteningProjection R.diagram)) R.comparison R.over_base))
      (relativeFunctorCurry f hf ≫ HomotopyLimits.relativeFunctorPost q
        (leftUnstraighteningProjection S.diagram) S.comparison S.over_base p) := by
  have hf' : (f ≫ S.comparison) ≫ leftUnstraighteningProjection S.diagram = fst E K ≫ p := by
    rw [Category.assoc, S.over_base, hf]
  have hw₀ : (prismEndpoint 0 E ▷ K) ≫ w.prism =
      fst E K ≫ R.comparison ≫ pullback.fst pointedSpaceProjection R.diagram := w.source
  have hw₁ : (prismEndpoint 1 E ▷ K) ≫ w.prism =
      (f ≫ S.comparison) ≫ pullback.fst pointedSpaceProjection S.diagram := by
    simpa only [LeftTransportRepresentation.pointedMap, Category.assoc] using w.target
  have e := unstraighteningSourceFamilyComparisonIso R.diagram S.diagram p R.comparison
    R.over_base t (f ≫ S.comparison) hf' w.prism hw₀ hw₁ w.projection
  have hc : relativeFunctorCurry (f ≫ S.comparison) hf' =
      relativeFunctorCurry f hf ≫ HomotopyLimits.relativeFunctorPost q
        (leftUnstraighteningProjection S.diagram) S.comparison S.over_base p := by
    apply relativeFunctorUncurry_injective (leftUnstraighteningProjection S.diagram) p
    rw [relativeFunctorUncurry_curry, relativeFunctorPost_uncurry,
      relativeFunctorUncurry_curry]
  rw [hc] at e
  exact e

/-- 概要：写像空間比較の後の unstraightening と始域前合成は標的後合成と関手同型。
方針：全相対射の普遍族を実現する同じ証拠に族の比較を適用する。
規約：相対写像空間全体で一つの可換式を与える。
使われ方：前後合成の同値性から比較射自体の同値性を得る。 -/
def transportRepresentationMappingSpaceMap_comparisonIso {E F B : SSet.{u + 1}}
    {p : E ⟶ B} {q : F ⟶ B} [LeftFibration p] [LeftFibration q]
    (hp : HasSmallSimplexFibers p) (hq : HasSmallSimplexFibers q)
    (R : LeftTransportRepresentation p) (S : LeftTransportRepresentation q) :
    FunctorIso (transportRepresentationMappingSpaceMap hp hq R S ≫
      leftUnstraighteningMappingSpaceMap R.diagram S.diagram ≫
      relativeFunctorOverPre (leftUnstraighteningProjection S.diagram)
        (Over.homMk (U := Over.mk p)
          (V := Over.mk (leftUnstraighteningProjection R.diagram)) R.comparison R.over_base))
      (HomotopyLimits.relativeFunctorPost q (leftUnstraighteningProjection S.diagram)
        S.comparison S.over_base p) := by
  let Y := relativeFunctorSpace q p
  let f := relativeFunctorUncurry (𝟙 Y)
  have hf := relativeFunctorUncurry_projection (𝟙 Y)
  have e := transportRepresentationFamilyComparisonIso R S
    (transportRepresentationMappingSpaceMap hp hq R S) f hf
    (transportRepresentationMappingSpaceWitness hp hq R S)
  have hc : relativeFunctorCurry f hf = 𝟙 Y := by
    apply relativeFunctorUncurry_injective q p
    exact relativeFunctorUncurry_curry f hf
  simpa only [hc, Y, Category.id_comp, Category.assoc] using e

end SerrePositivity.InfinityCategories
