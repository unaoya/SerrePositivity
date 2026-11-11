module

public import SerrePositivity.KST.Spectra.RawSpectrumStrictInterval

/-!
概要：内部 Hom 値の全列区間から、元の全 Hom に値を取る全パラメータのホモトピーを構成する。
方針：元の全 Hom の実辺を cotensor 比較で写し、元の写像空間の辺として評価する。
規約：各段のホモトピーからは推論しない。使われ方：全パラメータの比較の同値性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.KST.Spectra.PointedMapping

/-- 単位族を評価した射の頂点は、元の単位族の同じ非基点。 -/
lemma familyVertex_uncurry' {A E : PointedSimplicialSet.{u}}
    (a : 𝟙_ PointedSimplicialSet.{u} ⟶ PointedObject.basedHom A E) :
    familyVertex (uncurry' a) = PointedSimplicialSet.unitVertexEquiv _ a := by
  rw [familyVertex_eq_pointedHomVertex]
  change PointedSimplicialSet.unitVertexEquiv (PointedObject.basedHom A E)
    (curry' (X := A) (Y := E) (uncurry' (X := A) (Y := E) a)) = _
  rw [curry'_uncurry']

end SerrePositivity.KST.Spectra.PointedMapping

namespace SerrePositivity.KST.Spectra.RawSpectrumMapping
variable (X : OmegaSpectrum.{u}) (Y : KanSequence.{u}) (A : PointedSimplicialSet.{u})

/-- 元の cotensor 比較は、同じパラメータ族の頂点そのものを与える。 -/
lemma parameterFamily_vertex
    (f : KanSequence.Hom X.toKanSequence (KanSequence.mapping A Y)) :
    (cotensorComparison X Y A).right.app _
        (PointedSimplicialSet.unitVertexEquiv _ (homPoint X (KanSequence.mapping A Y) f)) =
      PointedMapping.familyVertex (parameterFamily X Y A f) := by
  rw [← PointedSimplicialSet.unitVertexEquiv_naturality]
  exact (PointedMapping.familyVertex_uncurry'
    (homPoint X (KanSequence.mapping A Y) f ≫ cotensorComparison X Y A)).symm

variable {f g : KanSequence.Hom X.toKanSequence (KanSequence.mapping A Y)}
  (H : KanSequence.StrictInterval f g)

/-- 同じ全列区間を、元の全 Hom に値を取る族の間の実際の写像空間の辺へ移す。 -/
def strictParameterIntervalEdge : (PointedObject.basedHom A (pointedSpace X Y)).right.Edge
    (PointedMapping.familyVertex (parameterFamily X Y A f))
    (PointedMapping.familyVertex (parameterFamily X Y A g)) :=
  ((strictIntervalEdge X (KanSequence.mapping A Y) H).map (cotensorComparison X Y A).right).ofEq
    (parameterFamily_vertex X Y A f) (parameterFamily_vertex X Y A g)

/-- 元の全 Hom の全パラメータ族の間の、実際の基点固定ホモトピー。 -/
def strictParameterHomotopy : SSet.Homotopy (parameterFamily X Y A f).right
    (parameterFamily X Y A g).right :=
  PointedMapping.homotopyOfEdge (strictParameterIntervalEdge X Y A H)

/-- ホモトピーは元の全 Hom の基点を全区間で固定する。 -/
lemma strictParameterHomotopy_base :
    A.hom ▷ (Δ[1] : SSet.{u}) ≫ (strictParameterHomotopy X Y A H).h =
      toUnit (𝟙_ SSet.{u} ⊗ (Δ[1] : SSet.{u})) ≫ (pointedSpace X Y).hom :=
  PointedMapping.homotopyOfEdge_base (strictParameterIntervalEdge X Y A H)

/-- 任意の元の族の cotensor 列の間に整合区間を構成すれば、元の族の実ホモトピーが得られる。 -/
lemma exists_pointedHomotopy_of_strictInterval
    (c d : A ⟶ pointedSpace X Y)
    (H : KanSequence.StrictInterval (homOfParameterFamily X Y A c) (homOfParameterFamily X Y A d)) :
    ∃ V : SSet.Homotopy c.right d.right,
      A.hom ▷ (Δ[1] : SSet.{u}) ≫ V.h =
        toUnit (𝟙_ SSet.{u} ⊗ (Δ[1] : SSet.{u})) ≫ (pointedSpace X Y).hom := by
  have hex : ∃ V : SSet.Homotopy
      (parameterFamily X Y A (homOfParameterFamily X Y A c)).right
      (parameterFamily X Y A (homOfParameterFamily X Y A d)).right,
      A.hom ▷ (Δ[1] : SSet.{u}) ≫ V.h =
        toUnit (𝟙_ SSet.{u} ⊗ (Δ[1] : SSet.{u})) ≫ (pointedSpace X Y).hom :=
    ⟨strictParameterHomotopy X Y A H, strictParameterHomotopy_base X Y A H⟩
  have hc : (parameterFamily X Y A (homOfParameterFamily X Y A c)).right = c.right :=
    congrArg Under.Hom.right (parameterFamily_homOfParameterFamily X Y A c)
  have hd : (parameterFamily X Y A (homOfParameterFamily X Y A d)).right = d.right :=
    congrArg Under.Hom.right (parameterFamily_homOfParameterFamily X Y A d)
  rw [hc, hd] at hex
  exact hex

/-- 両端固定の実構造区間を厳密化し、元の全 Hom の全パラメータの実ホモトピーへ戻す。 -/
lemma exists_pointedHomotopy_of_interval_structure
    (c d : A ⟶ pointedSpace X Y)
    (k : ∀ n, (X.level n).space ⟶ ((KanSequence.mapping A Y).freePath.level n).space)
    (hk : ∀ n, k n ≫ (KanSequence.mappingPre _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freeBoundaryInclusion
        (KanSequence.mapping A Y)).app n =
      (KanSequence.intervalBoundaryPair (homOfParameterFamily X Y A c)
        (homOfParameterFamily X Y A d)).app n)
    (h : ∀ n, PointedMapping.VerticalPath
      ((KanSequence.mappingPre _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freeBoundaryInclusion (KanSequence.mapping A Y)).app (n + 1))
      (X.sigma n ≫ k (n + 1))
      (PointedSimplicialSet.circle.{u} ◁ k n ≫ (KanSequence.mapping A Y).freePath.sigma n)) :
    ∃ V : SSet.Homotopy c.right d.right,
      A.hom ▷ (Δ[1] : SSet.{u}) ≫ V.h =
        toUnit (𝟙_ SSet.{u} ⊗ (Δ[1] : SSet.{u})) ≫ (pointedSpace X Y).hom :=
  exists_pointedHomotopy_of_strictInterval X Y A c d
    (KanSequence.rectifyInterval X.sigma_mono (homOfParameterFamily X Y A c)
      (homOfParameterFamily X Y A d) k hk h)

end SerrePositivity.KST.Spectra.RawSpectrumMapping
