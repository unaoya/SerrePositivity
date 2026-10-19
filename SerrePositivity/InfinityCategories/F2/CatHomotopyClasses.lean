module

public import SerrePositivity.InfinityCategories.F2.CatFunctorCoreIso

/-!
概要：Cat_∞ の平行な辺の類の一致と元の関手同型の同値。
方針：coherent Hom 比較の連結成分上の単射性と core の頂点同型を使う。
規約：同じ二対象間の指定された関手を比較する。
使われ方：Cat_∞ の可逆辺から関手の実際の逆条件を回収する。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 概要：Cat_∞ のホモトピー圏で同じ射を表す関手は関手同型で結ばれる。
方針：写像空間の連結成分の単射性を通して core の連結成分を一致させる。
規約：元の関手 core の包含により、得られた頂点同型を関手同型へ送る。
使われ方：Cat_∞ の辺の可逆性の反映。 -/
lemma catInfinity_functorIso_of_homMk_eq {X Y : QCat.{u}} {f g : X ⟶ Y}
    (h : SSet.Truncated.HomotopyCategory.homMk (coherentNerveEdge f).toTruncated =
      SSet.Truncated.HomotopyCategory.homMk (coherentNerveEdge g).toTruncated) :
    Nonempty (FunctorIso f g) := by
  let a := ULift.up.{u + 1} (SimplicialCategory.homEquiv' X Y f)
  let b := ULift.up.{u + 1} (SimplicialCategory.homEquiv' X Y g)
  have hf : pinchedHomVertexEquiv _ _
      ((coherentHomComparison X Y).app _ a) = (coherentNerveEdge f).toTruncated := by
    apply SSet.Truncated.Edge.ext
    exact coherentHomComparison_ordinary f
  have hg : pinchedHomVertexEquiv _ _
      ((coherentHomComparison X Y).app _ b) = (coherentNerveEdge g).toTruncated := by
    apply SSet.Truncated.Edge.ext
    exact coherentHomComparison_ordinary g
  have hp : SSet.mapπ₀ (coherentHomComparison X Y) (SSet.π₀.mk a) =
      SSet.mapπ₀ (coherentHomComparison X Y) (SSet.π₀.mk b) := by
    apply pinchedHomPiZeroToHom_injective (coherentNerveVertex X) (coherentNerveVertex Y)
    change SSet.Truncated.HomotopyCategory.homMk
      (pinchedHomVertexEquiv _ _ ((coherentHomComparison X Y).app _ a)) =
      SSet.Truncated.HomotopyCategory.homMk
        (pinchedHomVertexEquiv _ _ ((coherentHomComparison X Y).app _ b))
    rwa [hf, hg]
  have hp :=
    (coherentHomComparison_isSimplicialHomotopyEquivalence X Y).mapPiZero_bijective.injective hp
  have hq := congrArg (coherentUliftPiZeroDown (SimplicialCategory.sHom X Y)) hp
  change SSet.π₀.mk (SimplicialCategory.homEquiv' X Y f) =
    SSet.π₀.mk (SimplicialCategory.homEquiv' X Y g) at hq
  obtain ⟨e⟩ := coherentVertexIso_of_piZero_eq hq
  exact ⟨e.map (quasicategoryCore ((ihom X.obj).obj Y.obj)).ι⟩

/-- 概要：Cat_∞ の平行な辺の類の一致は関手同型の存在と同値。
方針：写像空間比較による反映と、core の頂点同型による保存を組み合わせる。
規約：可逆な自然変換の存在であり、関手の厳密な等号にはしない。
使われ方：Cat_∞ のホモトピー圏の逆条件の具体化。 -/
lemma catInfinity_homMk_eq_iff_functorIso {X Y : QCat.{u}} {f g : X ⟶ Y} :
    SSet.Truncated.HomotopyCategory.homMk (coherentNerveEdge f).toTruncated =
      SSet.Truncated.HomotopyCategory.homMk (coherentNerveEdge g).toTruncated ↔
        Nonempty (FunctorIso f g) := by
  constructor
  · exact catInfinity_functorIso_of_homMk_eq
  · rintro ⟨h⟩
    exact coherentNerveEdge_homMk_eq_of_enrichedVertexIso (catInfinityFunctorCoreVertexIso h)

end SerrePositivity.InfinityCategories.F2
