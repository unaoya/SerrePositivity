module

public import SerrePositivity.InfinityCategories.F1.KanModels.KanEnrichedComparisonIndexTriangle
public import SerrePositivity.InfinityCategories.F1.KanModels.KanEnrichedDiagramEdges
public import SerrePositivity.InfinityCategories.F1.Diagrams.RelativeSectionDiagram

/-!
概要：豊穣比較の図式を一本の射へ制限して既存の比較の族を回収する。
方針：二点の対象と混合 Hom、全高次の対角評価を順に同定する。
規約：対象ごとの辺の一致から全体の一致を推論しない。
使われ方：降下した straightening と既存 transport の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory MonoidalCategory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories

/-- 概要：一本の射を二点図式として選ぶ添字関手。
方針：持ち上げた有限順序から composable arrows へ合成する。
規約：両端を元の始点と終点へ送る。
使われ方：任意の豊穣図式の辺への制限。 -/
def kanEnrichedDiagramArrowIndex {J : Type u} [Category.{u} J]
    {i j : J} (f : i ⟶ j) : ULift.{u} (Fin 2) ⥤ J :=
  (⟨ULift.down, fun _ _ h ↦ h⟩ : ULift.{u} (Fin 2) →o Fin 2).toFunctor ⋙
    ComposableArrows.mk₁ f

/-- 概要：射への制限の対象は既存の比較の対象。
方針：二点を分けて計算する。
規約：対象の厳密な等式。
使われ方：混合 Hom の始域と終域の同定。 -/
lemma KanEnrichedDiagram.arrow_object {C : Type v} [Category.{u} C]
    [SimplicialCategory C] {J : Type u} [Category.{u} J]
    (D : KanEnrichedDiagram C J) {i j : J} (f : i ⟶ j) (X : C)
    (s : ULift.{u} (Fin 2)) :
    (D.obj ((kanEnrichedDiagramArrowIndex f).obj s)).obj X =
      (kanEnrichedComparisonDiagram (D.map f) X).obj s := by
  rcases s with ⟨s⟩
  fin_cases s <;> rfl

/-- 概要：射への制限の混合 Hom は比較の混合 Hom。
方針：端点の四通りを分け、退化では恒等則を使う。
規約：全高次の Hom に対する等式。
使われ方：共同対角評価の一致。 -/
lemma KanEnrichedDiagram.arrow_mixedHom {C : Type v} [Category.{u} C]
    [SimplicialCategory C] {J : Type u} [Category.{u} J]
    (D : KanEnrichedDiagram C J) {i j : J} (f : i ⟶ j) (X Y : C)
    {s t : ULift.{u} (Fin 2)} (g : s ⟶ t) :
    (D.mappingSpaceMap X Y ≫
      strictDiagramMixedHom ((kanEnrichedDiagramArrowIndex f).map g)
        (D.evaluate X ⋙ kanObjectForget) (D.evaluate Y ⋙ kanObjectForget)) ≫
      eqToHom (congrArg₂ (fun U V : KanObject.{u} ↦ SimplicialCategory.sHom U V)
        (D.arrow_object f X s) (D.arrow_object f Y t)) =
    kanEnrichedComparisonMappingSpaceMap (D.map f) X Y ≫ strictDiagramMixedHom g
      (kanEnrichedComparisonDiagram (D.map f) X ⋙ kanObjectForget)
      (kanEnrichedComparisonDiagram (D.map f) Y ⋙ kanObjectForget) := by
  rcases s with ⟨s⟩
  rcases t with ⟨t⟩
  fin_cases s <;> fin_cases t
  all_goals simp only [eqToHom_refl, Category.comp_id]
  all_goals first
    | (have h := leOfHom g; change (1 : ℕ) ≤ 0 at h; omega)
    | rfl
    | (simp only [strictDiagramMixedHom]
       change _ ≫ (ihom _).map (kanObjectForget.map ((D.map (𝟙 _)).val Y)) = _
       rw [D.map_id]
       rfl)

/-- 概要：射への制限の共同対角評価は比較の共同対角評価。
方針：全高次の混合 Hom の一致を対角評価へ適用する。
規約：対象の coherent 図式は任意。
使われ方：関手空間全体で比較の族を回収する。 -/
lemma KanEnrichedDiagram.arrow_diagonal {C : Type v} [Category.{u} C]
    [SimplicialCategory C] {J : Type u} [Category.{u} J]
    (D : KanEnrichedDiagram C J) {i j : J} (f : i ⟶ j)
    {I : Type u} [LinearOrder I] (σ : I ⥤ ULift.{u} (Fin 2))
    (T : EnrichedFunctor SSet.{u} (SimplicialThickening I) C) :
    diagonalKanDiagramEvaluation (σ ⋙ (kanEnrichedDiagramArrowIndex f))
        (T.comp SSet D.toEnrichedFunctor) =
      diagonalKanDiagramEvaluation σ
        (T.comp SSet (kanEnrichedComparisonArrowEnriched (D.map f))) := by
  refine EnrichedFunctor.ext SSet
    (fun i ↦ D.arrow_object f (T.obj i) (σ.obj i.as)) ?_
  intro i j
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro P
  have hij : i.as ≤ j.as := SimplicialThickening.Path.le (P.obj 0)
  change ((diagonalKanDiagramHom (σ ⋙ (kanEnrichedDiagramArrowIndex f))
    (T.comp SSet D.toEnrichedFunctor) i j) ≫
      eqToHom _).app n P =
    (diagonalKanDiagramHom σ
      (T.comp SSet (kanEnrichedComparisonArrowEnriched (D.map f))) i j).app n P
  rw [diagonalKanDiagramHom_of_le _ _ i j hij, diagonalKanDiagramHom_of_le _ _ i j hij]
  change ((T.map i j ≫ D.mappingSpaceMap _ _) ≫
    strictDiagramMixedHom ((kanEnrichedDiagramArrowIndex f).map (σ.map (homOfLE hij)))
      _ _ ≫ eqToHom _).app n P = _
  rw [Category.assoc, ← Category.assoc _ _ (eqToHom _),
    D.arrow_mixedHom]
  rfl

/-- 概要：任意の豊穣図式の射への制限は元の比較の族。
方針：uncurry 後に全高次の対角評価を同定する。
規約：全対象と高次の射を同時に保つ厳密な等式。
使われ方：straightening の制限の辺を既存の比較へ戻す。 -/
lemma KanEnrichedDiagram.realization_arrow {C : Type (u + 1)} [Category.{u} C]
    [SimplicialCategory C] {J : Type u} [Category.{u} J]
    (D : KanEnrichedDiagram C J) {i j : J} (f : i ⟶ j) :
    D.realization ≫
      (pre ((SSet.uliftFunctor.{u + 1, u}).map
        (nerveMap (kanEnrichedDiagramArrowIndex f)))).app SpaceInfinity.{u} =
      kanEnrichedComparisonFamily (D.map f) := by
  apply uncurry_injective
  rw [uncurry_pre_app]
  simp only [KanEnrichedDiagram.realization, kanEnrichedComparisonFamily,
    uncurry_natural_left, kanDiagramRealization, uncurry_curry]
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨σ, T⟩
  exact D.arrow_diagonal f (kanDiagramSimplexBase σ.down) T

/-- 概要：一本の射の標準辺は二点添字の標準辺の像。
方針：通常の nerve の一単体を計算する。
規約：端点の証明によらず一単体そのものを比較する。
使われ方：比較の族の制限から実際の辺を回収する。 -/
lemma kanEnrichedDiagramArrowIndex_edge {J : Type u} [Category.{u} J]
    {i j : J} (f : i ⟶ j) :
    (coherentResolutionComparisonIndexEdge.map
      ((SSet.uliftFunctor.{u + 1, u}).map
        (nerveMap (kanEnrichedDiagramArrowIndex f)))).edge =
      (kanEnrichedDiagramIndexEdge f).edge := by
  change ULift.up ((ComposableArrows.mk₁ (homOfLE
    (show (ULift.up (0 : Fin 2) : ULift.{u} (Fin 2)) ≤ ULift.up 1 by decide))) ⋙
      kanEnrichedDiagramArrowIndex f) = ULift.up (ComposableArrows.mk₁ f)
  apply ULift.ext
  apply CategoryTheory.Functor.ext
  · intro a b g
    fin_cases a <;> fin_cases b
    all_goals simp only [eqToHom_refl, Category.comp_id, Category.id_comp]
    all_goals rfl
  · intro a
    fin_cases a <;> rfl

/-- 概要：豊穣図式の実現の辺は既存の豊穣比較の辺そのもの。
方針：共同実現の制限公式と標準添字の辺の公式を合成する。
規約：全対象の関手空間での厳密な等式。
使われ方：単体圏の制限の辺を切断評価の比較へ戻す。 -/
lemma KanEnrichedDiagram.realizationEdge_eq {C : Type (u + 1)} [Category.{u} C]
    [SimplicialCategory C] {J : Type u} [Category.{u} J]
    (D : KanEnrichedDiagram C J) {i j : J} (f : i ⟶ j) :
    D.realizationEdge f = kanEnrichedComparisonEdge (D.map f) := by
  apply SSet.Edge.ext
  have h := congrArg transposeFunctorFamily (D.realization_arrow f)
  rw [transposeFunctorFamily_pre] at h
  have h' := congrArg (fun m ↦ m.app (Opposite.op (SimplexCategory.mk 1))
    coherentResolutionComparisonIndexEdge.edge) h
  change (transposeFunctorFamily D.realization).app _
    (kanEnrichedDiagramIndexEdge f).edge = _
  rw [← kanEnrichedDiagramArrowIndex_edge f]
  exact h'

/-- 概要：共同切断評価の辺は相対前合成の豊穣比較の辺。
方針：任意の豊穣図式の辺の一致を切断図式へ特殊化する。
規約：関手空間の一単体そのものの等式。
使われ方：底の単体の制限に関する降下比較。 -/
lemma relativeSectionDiagramInfinity_edge {B : SSet.{u}} {J : Type u}
    [Category.{u} J] (A : Jᵒᵖ ⥤ Over B) {i j : J} (f : i ⟶ j) :
    ((kanEnrichedDiagramIndexEdge f).map (relativeSectionDiagramInfinity A)).edge =
      (kanEnrichedComparisonEdge (relativeFunctorOverPreComparison (A.map f.op))).edge :=
  congrArg SSet.Edge.edge ((relativeSectionEnrichedDiagram A).realizationEdge_eq f)

end SerrePositivity.InfinityCategories



