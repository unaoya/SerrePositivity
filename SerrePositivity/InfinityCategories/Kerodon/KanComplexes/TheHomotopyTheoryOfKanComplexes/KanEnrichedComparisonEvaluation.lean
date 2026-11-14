module

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.KanEnrichedRealizationValue
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.SimplexSectionBaseChange
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.KanDiagramOrdinaryEdgePrism

/-!
概要：共同比較の指定辺を一つの係数対象へ制限して元の自然変換の辺を回収する。
方針：任意の底単体と区間パラメーターで同じ対角評価を計算する。
規約：各頂点の一致だけに弱めず、指定辺の一単体そのものを比較する。
使われ方：Kerodon §3.1（Tag 00SZ）・Corollary 5.6.0.6（Tag 028T）の
共同実現を使う、標準貼り合わせ同型の分類像の係数移送。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local implicit_reducible] Monotone
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
open Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
open Kerodon.ExamplesOfInfinityCategories.SimplicialCategories
open Kerodon.FibrationsOfInfinityCategories.CartesianFibrations
open Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence
open Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors
namespace SerrePositivity.InfinityCategories.Kerodon.KanComplexes
namespace TheHomotopyTheoryOfKanComplexes

private lemma coefficient_diagonal_constant
    {C : Type (u + 1)} [Category.{u} C] [SimplicialCategory C]
    {J : Type u} [Category.{u} J] (D : KanEnrichedDiagram C J)
    (X : C) {n : ℕ} (σ : (nerve J) _⦋n⦌) :
    diagonalKanDiagramEvaluation (kanDiagramSimplexBase σ)
      ((Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant
        (coherentNerveVertex X) n).comp SSet D.toEnrichedFunctor) =
      enrichedFunctorOfOrderDiagram (kanDiagramSimplexBase σ ⋙ D.evaluate X) := by
  change kanDiagramDiagonalSimplex σ
    ((coherentNerveMap D.toEnrichedFunctor).app (Opposite.op ⦋n⦌)
      (Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant
        (coherentNerveVertex X) n)) = _
  rw [pinchedConstant_map,
    coherentNerveMap_vertex, kanDiagramDiagonalSimplex_constant]
  rfl


private lemma enriched_map_app_heq {I : Type u} [LinearOrder I]
    {F G : EnrichedFunctor SSet.{u} (SimplicialThickening I) KanObject.{u}}
    (h : F = G) (i j : SimplicialThickening I) (d : SimplexCategoryᵒᵖ)
    (P : (SimplicialCategory.sHom i j).obj d) :
    HEq ((F.map i j).app d P) ((G.map i j).app d P) := by
  cases h
  rfl

private lemma post_constant {A B C : SSet.{u}} (f : A ⟶ B) (g : B ⟶ C)
    (d : SimplexCategoryᵒᵖ) :
    ((ihom A).map g).app d
      (Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant
        (functorVertex f) d.unop.len) =
      Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant
        (functorVertex (f ≫ g)) d.unop.len := by
  apply CategoryTheory.Functor.functorHom_ext
  intro k α
  apply ConcreteCategory.hom_ext
  intro x
  rfl

/-- 二変数を交換した族の円柱は元の族のuncurry。同じ二変数評価の証明分割。 -/
private lemma prism_transpose {A I X : SSet.{u}} (F : A ⟶ (ihom I).obj X) :
    functorFamilyPrism (transposeFunctorFamily F) = uncurry F := by
  rw [functorFamilyPrism, transposeFunctorFamily, uncurry_curry]
  simp only [← Category.assoc, SymmetricCategory.symmetry, Category.id_comp]

/-- 概要：指定共同比較の元の辺は係数対象への制限で元の自然変換の辺になる。
方針：関手空間の一単体の全パラメーターで、同じ混合対角評価を比較する。
規約：任意の添字圏と豊穣圏を許す。対象ごとに別の辺を選ばない。
使われ方：元の反復引き戻し比較による指定切断同型を、その分類射へ照合する。 -/
lemma KanEnrichedDiagramComparison.jointComparisonEdge_restrict
    {C : Type (u + 1)} [Category.{u} C] [SimplicialCategory C]
    {J : Type u} [Category.{u} J] {D E : KanEnrichedDiagram C J}
    (η : KanEnrichedDiagramComparison D E) (X : C) :
    ((pre (lift (𝟙 ((SSet.uliftFunctor.{u + 1, u}).obj (nerve J)))
      (SSet.const (coherentNerveVertex X)))).app SpaceInfinity.{u}).app (Opposite.op ⦋1⦌)
        η.jointComparisonEdge.edge =
      (kanDiagramNaturalTransformationEdge
        (F := ⟨D.evaluate X, trivial⟩) (G := ⟨E.evaluate X, trivial⟩) (η.app X)).edge := by
  change (transposeFunctorFamily η.jointComparisonFamily ≫
      (pre (lift (𝟙 ((SSet.uliftFunctor.{u + 1, u}).obj (nerve J)))
        (SSet.const (coherentNerveVertex X)))).app SpaceInfinity.{u}).app (Opposite.op ⦋1⦌)
      coherentResolutionComparisonIndexEdge.edge = _
  rw [← transposeFunctorFamily_comp]
  apply (SSet.yonedaEquiv (X := (ihom
    ((SSet.uliftFunctor.{u + 1, u}).obj (nerve J))).obj SpaceInfinity.{u})
      (n := ⦋1⦌)).symm.injective
  apply uncurry_injective
  apply (cancel_epi (β_ (Δ[1] : SSet.{u + 1})
    ((SSet.uliftFunctor.{u + 1, u}).obj (nerve J))).hom).mp
  change functorFamilyPrism (SSet.yonedaEquiv.symm
      ((transposeFunctorFamily
        (lift (𝟙 ((SSet.uliftFunctor.{u + 1, u}).obj (nerve J)))
          (SSet.const (coherentNerveVertex X)) ≫ η.jointComparisonFamily)).app
            (Opposite.op ⦋1⦌) coherentResolutionComparisonIndexEdge.edge)) =
    functorEdgePrism (kanDiagramNaturalTransformationEdge
      (F := ⟨D.evaluate X, trivial⟩) (G := ⟨E.evaluate X, trivial⟩) (η.app X))
  rw [← SSet.yonedaEquiv_symm_comp, ← functorFamilyPrism_restrict, prism_transpose]
  rw [kanDiagramNaturalTransformationEdge_prism
    (F := ⟨D.evaluate X, trivial⟩) (G := ⟨E.evaluate X, trivial⟩) (η.app X)]
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨t, σ⟩
  change kanDiagramDiagonalSimplex
      ((nerve (ULift.{u} (Fin 2))).map (stdSimplex.objEquiv t).op
        coherentResolutionComparisonIndexEdge.edge.down)
      ((KanDiagramNerve (ULift.{u} (Fin 2))).map (𝟙 (Opposite.op ⦋n⦌))
        (η.diagonalArrow (kanDiagramSimplexBase σ.down)
          (Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant
            (coherentNerveVertex X) n))) =
    enrichedFunctorOfOrderDiagram
      (kanDiagramEdgeOrderDiagram
        (F := ⟨D.evaluate X, trivial⟩) (G := ⟨E.evaluate X, trivial⟩)
        (η.app X) σ.down (stdSimplex.objEquiv t))
  rw [Functor.map_id_apply]
  have ho : ∀ i,
      (kanDiagramDiagonalSimplex
        ((nerve (ULift.{u} (Fin 2))).map (stdSimplex.objEquiv t).op
          coherentResolutionComparisonIndexEdge.edge.down)
        (η.diagonalArrow (kanDiagramSimplexBase σ.down)
          (Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant
            (coherentNerveVertex X) n))).obj i =
      (enrichedFunctorOfOrderDiagram (kanDiagramEdgeOrderDiagram
        (F := ⟨D.evaluate X, trivial⟩) (G := ⟨E.evaluate X, trivial⟩)
        (η.app X) σ.down (stdSimplex.objEquiv t))).obj i := by
    intro i
    let a := (stdSimplex.objEquiv t).toOrderHom i.as.down
    let j := σ.down.obj i.as.down
    change ((ComposableArrows.mk₁ (show (D.evaluate X).obj j ⟶ (E.evaluate X).obj j from
        (η.app X).app j)).obj (coherentResolutionComparisonIndexEdge.edge.down.obj a).down) =
      ((ComposableArrows.mk₁ (kanDiagramUnderlyingTransformation
        (F := ⟨D.evaluate X, trivial⟩) (G := ⟨E.evaluate X, trivial⟩)
        (η.app X))).obj a).obj j
    have hi : (coherentResolutionComparisonIndexEdge.edge.down.obj a).down = a := by
      generalize a = b
      fin_cases b <;> rfl
    rw [hi]
    generalize a = b
    fin_cases b <;> rfl
  refine EnrichedFunctor.ext SSet ho ?_
  intro i j
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro P
  have hij : i.as ≤ j.as := SimplicialThickening.Path.le (P.obj 0)
  have hcast {A B D : SSet.{u}} (f : A ⟶ B) (h : B = D)
      (k : SimplexCategoryᵒᵖ) (x : A.obj k) :
      HEq ((f ≫ eqToHom h).app k x) (f.app k x) := by
    subst D
    rfl
  apply eq_of_heq
  refine (hcast _ _ d P).trans ?_
  change HEq ((diagonalKanDiagramHom
      (kanDiagramSimplexBase ((nerve (ULift.{u} (Fin 2))).map (stdSimplex.objEquiv t).op
        coherentResolutionComparisonIndexEdge.edge.down)) _ i j).app d P) _
  erw [diagonalKanDiagramHom_of_le _ _ i j hij]
  let δ := η.diagonalKanComparison (kanDiagramSimplexBase σ.down)
    (Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant
      (coherentNerveVertex X) n)
  let A := kanDiagramSimplexBase ((nerve (ULift.{u} (Fin 2))).map
    (stdSimplex.objEquiv t).op coherentResolutionComparisonIndexEdge.edge.down)
  change HEq ((((ihom ((kanEnrichedComparisonDiagram δ i).obj (A.obj i.as)).obj).map
      ((kanEnrichedComparisonDiagram δ j).map (A.map (homOfLE hij)))).app d)
        ((kanEnrichedComparisonMappingSimplex δ i j P).val (A.obj i.as))) _
  have hA : A =
      (⟨ULift.down, fun _ _ h ↦ h⟩ :
        ULift.{u} (Fin (n + 1)) →o Fin (n + 1)).toFunctor ⋙
        (stdSimplex.objEquiv t).toOrderHom.toFunctor ⋙
          coherentResolutionComparisonIndexEdge.edge.down := by rfl
  rw [hA]
  have hIndex : coherentResolutionComparisonIndexEdge.edge.down =
      (⟨ULift.up, fun _ _ h ↦ h⟩ : Fin 2 →o ULift.{u} (Fin 2)).toFunctor := by
    refine CategoryTheory.Functor.ext (fun c ↦ ?_) (fun _ _ _ ↦ Subsingleton.elim _ _)
    fin_cases c <;> rfl
  rw [hIndex]
  have hab := (stdSimplex.objEquiv t).toOrderHom.monotone
    (show i.as.down ≤ j.as.down from hij)
  change HEq
    ((((ihom ((ComposableArrows.mk₁ (δ.val i)).obj
        ((stdSimplex.objEquiv t).toOrderHom i.as.down)).obj).map
      ((ComposableArrows.mk₁ (δ.val j)).map (homOfLE hab))).app d)
        ((kanEnrichedComparisonMappingSimplex δ i j P).val
          (ULift.up ((stdSimplex.objEquiv t).toOrderHom i.as.down))))
    (Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant
      (SimplicialCategory.homEquiv' _ _
        (((ComposableArrows.mk₁ (kanDiagramUnderlyingTransformation
          (F := ⟨D.evaluate X, trivial⟩) (G := ⟨E.evaluate X, trivial⟩)
          (η.app X))).map (homOfLE hab)).app (σ.down.obj i.as.down) ≫
          ((ComposableArrows.mk₁ (kanDiagramUnderlyingTransformation
            (F := ⟨D.evaluate X, trivial⟩) (G := ⟨E.evaluate X, trivial⟩)
            (η.app X))).obj ((stdSimplex.objEquiv t).toOrderHom j.as.down)).map
              (σ.down.map (homOfLE (show i.as.down ≤ j.as.down from hij))))) d.unop.len)
  have hDij : ((diagonalKanDiagramEvaluation (kanDiagramSimplexBase σ.down)
      ((Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant
        (coherentNerveVertex X) n).comp SSet D.toEnrichedFunctor)).map i j).app d P =
      Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant
        (functorVertex ((D.evaluate X).map
          (σ.down.map (homOfLE (show i.as.down ≤ j.as.down from hij)))) ) d.unop.len :=
    eq_of_heq (enriched_map_app_heq (coefficient_diagonal_constant D X σ.down) i j d P)
  have hEij : ((diagonalKanDiagramEvaluation (kanDiagramSimplexBase σ.down)
      ((Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant
        (coherentNerveVertex X) n).comp SSet E.toEnrichedFunctor)).map i j).app d P =
      Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant
        (functorVertex ((E.evaluate X).map
          (σ.down.map (homOfLE (show i.as.down ≤ j.as.down from hij)))) ) d.unop.len :=
    eq_of_heq (enriched_map_app_heq (coefficient_diagonal_constant E X σ.down) i j d P)
  generalize hai : (stdSimplex.objEquiv t).toOrderHom i.as.down = ai at *
  generalize hbj : (stdSimplex.objEquiv t).toOrderHom j.as.down = bj at *
  fin_cases ai <;> fin_cases bj
  · exact heq_of_eq hDij
  · change HEq
      (((ihom ((D.evaluate X).obj (σ.down.obj i.as.down)).obj).map
        ((η.app X).app (σ.down.obj j.as.down))).app d
          (((diagonalKanDiagramEvaluation (kanDiagramSimplexBase σ.down)
            ((Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant
              (coherentNerveVertex X) n).comp SSet D.toEnrichedFunctor)).map i j).app d P))
      (Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant
        (functorVertex ((η.app X).app (σ.down.obj i.as.down) ≫
          (E.evaluate X).map (σ.down.map (homOfLE (show i.as.down ≤ j.as.down from hij)))))
          d.unop.len)
    apply heq_of_eq
    rw [hDij, post_constant]
    exact congrArg
      (fun f : ((D.evaluate X).obj (σ.down.obj i.as.down)).obj ⟶
          ((E.evaluate X).obj (σ.down.obj j.as.down)).obj ↦
        Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant
          (functorVertex f) d.unop.len)
      ((η.app X).naturality (σ.down.map (homOfLE (show i.as.down ≤ j.as.down from hij))))
  · exact False.elim ((by decide : ¬ (1 : Fin 2) ≤ 0) hab)
  · exact heq_of_eq hEij

end TheHomotopyTheoryOfKanComplexes
end SerrePositivity.InfinityCategories.Kerodon.KanComplexes
