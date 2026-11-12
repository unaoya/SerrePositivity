module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.KanEnrichedComparisonIso

/-!
概要：豊穣自然な比較の通常の図式を Kan 値図式への豊穣関手に束ねる。
方針：各対象の通常の図式を作り、高次 Hom の作用を全成分で与える。
規約：添字は任意の小圏。二点に限定しない。
使われ方：比較の合成・恒等・高次の列を一つの coherent な族に実現する。

対応節は Kerodon 3.1（Tag 00SZ）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory MonoidalCategory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes

/-- 概要：Kan 値豊穣関手と豊穣自然な比較の通常の図式。
方針：比較の恒等・合成を全対象で厳密に保持する。
規約：自然性は全高次の豊穣 Hom に関する。
使われ方：比較の列を同時に coherent nerve へ実現する入力。 -/
structure KanEnrichedDiagram (C : Type v) [Category.{u} C] [SimplicialCategory C]
    (J : Type u) [Category.{u} J] where
  obj : J → EnrichedFunctor SSet.{u} C _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}
  map : ∀ {i j : J}, (i ⟶ j) → _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.KanEnrichedComparison (obj i) (obj j)
  map_id : ∀ i X, (map (𝟙 i)).val X = 𝟙 ((obj i).obj X)
  map_comp : ∀ {i j k : J} (f : i ⟶ j) (g : j ⟶ k) X,
    (map (f ≫ g)).val X = (map f).val X ≫ (map g).val X

/-- 概要：比較の図式を一つの対象で評価して通常の Kan 値図式にする。
方針：図式に記録した恒等・合成の条件をそのまま使う。
規約：対象の図式を独立に選ばない。
使われ方：図式値豊穣関手の対象への作用。 -/
def KanEnrichedDiagram.evaluate {C : Type v} [Category.{u} C] [SimplicialCategory C]
    {J : Type u} [Category.{u} J] (D : KanEnrichedDiagram C J) (X : C) : J ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u} where
  obj j := (D.obj j).obj X
  map f := (D.map f).val X
  map_id j := D.map_id j X
  map_comp f g := D.map_comp f g X

/-- 概要：一つの高次 Hom の単体は全成分で整合する strict な変換を与える。
方針：各成分の豊穣作用と比較の豊穣自然性を使う。
規約：添字圏の全ての射に関して自然。
使われ方：Kan 図式値の豊穣 Hom の作用の単体。 -/
def KanEnrichedDiagram.mappingSimplex {C : Type v} [Category.{u} C] [SimplicialCategory C]
    {J : Type u} [Category.{u} J] (D : KanEnrichedDiagram C J) (X Y : C)
    {n : SimplexCategoryᵒᵖ} (θ : (SimplicialCategory.sHom X Y).obj n) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.strictDiagramMappingSimplex (D.evaluate X ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget)
      (D.evaluate Y ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget) n := by
  refine ⟨fun j ↦ ((D.obj j).map X Y).app n θ, ?_⟩
  intro i j f k α x
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.kanEnrichedComparison_app (D.map f) X Y θ α x).symm

/-- 概要：豊穣 Hom を図式間の全 strict 変換空間へ写す。
方針：各成分の単体的自然性を同時に適用する。
規約：頂点の射だけへの制限は行わない。
使われ方：図式値豊穣関手の Hom の作用。 -/
def KanEnrichedDiagram.mappingSpaceMap {C : Type v} [Category.{u} C] [SimplicialCategory C]
    {J : Type u} [Category.{u} J] (D : KanEnrichedDiagram C J) (X Y : C) :
    SimplicialCategory.sHom X Y ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.strictDiagramMappingSpace
      (D.evaluate X ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget) (D.evaluate Y ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget) where
  app _ := ↾D.mappingSimplex X Y
  naturality {n m} α := by
    apply ConcreteCategory.hom_ext
    intro θ
    apply Subtype.ext
    funext j
    exact congrArg (fun f : (SimplicialCategory.sHom X Y).obj n ⟶
      ((ihom ((D.obj j).obj X).obj).obj ((D.obj j).obj Y).obj).obj m ↦ f θ)
      (((D.obj j).map X Y).naturality α)

/-- 概要：豊穣比較の図式は通常の Kan 図式を値とする一つの豊穣関手。
方針：成分ごとの単位則・合成則を strict 変換空間で同時に使う。
規約：任意の添字圏を扱い、二点図式の場合も含む。
使われ方：全対象を同時に動かす比較の列の coherent な実現。 -/
def KanEnrichedDiagram.toEnrichedFunctor {C : Type v}
    [Category.{u} C] [SimplicialCategory C] {J : Type u} [Category.{u} J]
    (D : KanEnrichedDiagram C J) :
    EnrichedFunctor SSet.{u} C (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.KanDiagramObject J) where
  obj X := ⟨D.evaluate X, trivial⟩
  map := D.mappingSpaceMap
  map_id X := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro t
    apply Subtype.ext
    funext j
    exact congrArg (fun f : 𝟙_ SSet.{u} ⟶
      (ihom ((D.obj j).obj X).obj).obj ((D.obj j).obj X).obj ↦ f.app n t)
      ((D.obj j).map_id X)
  map_comp X Y Z := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    rintro ⟨f, g⟩
    apply Subtype.ext
    funext j
    have h := congrArg (fun m : SimplicialCategory.sHom X Y ⊗ SimplicialCategory.sHom Y Z ⟶
      (ihom ((D.obj j).obj X).obj).obj ((D.obj j).obj Z).obj ↦ m.app n (f, g))
      ((D.obj j).map_comp X Y Z)
    apply CategoryTheory.Functor.functorHom_ext
    intro k α
    apply ConcreteCategory.hom_ext
    intro x
    have h' := congrArg (fun θ :
      ((ihom ((D.obj j).obj X).obj).obj ((D.obj j).obj Z).obj).obj n ↦ θ.app k α x) h
    change (((D.obj j).map X Z).app n ((eComp SSet X Y Z).app n (f, g))).app k α x =
      (((D.obj j).map Y Z).app n g).app k (α ≫ 𝟙 k)
        ((((D.obj j).map X Y).app n f).app k (α ≫ 𝟙 k) x) at h'
    rw [Category.comp_id] at h'
    exact h'

/-- 概要：任意の豊穣比較の図式を coherent な関手の族として実現する。
方針：図式値の豊穣関手の coherent nerve に共同評価を合成する。
規約：全添字と全対象を同時に保持する。
使われ方：比較の合成三角形と高次の列の実際の図式。 -/
def KanEnrichedDiagram.realization {C : Type (u + 1)} [Category.{u} C]
    [SimplicialCategory C] {J : Type u} [Category.{u} J] (D : KanEnrichedDiagram C J) :
    SimplicialNerve C ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinityFunctor
      ((SSet.uliftFunctor.{u + 1, u}).obj (nerve J)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap D.toEnrichedFunctor ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.kanDiagramRealization J

/-- 概要：比較の図式を任意の添字関手で制限する。
方針：対象と比較の両方へ同じ関手を作用させる。
規約：面と退化の両方を含む。
使われ方：実現した高次単体の指定面を回収する。 -/
def KanEnrichedDiagram.reindex {C : Type v} [Category.{u} C] [SimplicialCategory C]
    {J L : Type u} [Category.{u} J] [Category.{u} L]
    (D : KanEnrichedDiagram C J) (k : L ⥤ J) : KanEnrichedDiagram C L where
  obj i := D.obj (k.obj i)
  map f := D.map (k.map f)
  map_id i X := by rw [k.map_id]; exact D.map_id _ _
  map_comp f g X := by rw [k.map_comp]; exact D.map_comp _ _ _

/-- 概要：図式値の豊穣関手を一つの添字で評価すると元の豊穣関手に戻る。
方針：対象と Hom の同じ成分を計算する。
規約：豊穣関手の厳密な等式。
使われ方：実現した図式の全ての頂点を同定する。 -/
lemma KanEnrichedDiagram.toEnrichedFunctor_evaluate {C : Type v}
    [Category.{u} C] [SimplicialCategory C] {J : Type u} [Category.{u} J]
    (D : KanEnrichedDiagram C J) (j : J) :
    D.toEnrichedFunctor.comp SSet (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.kanDiagramEvaluationEnriched j) = D.obj j := by
  refine EnrichedFunctor.ext SSet (fun _ ↦ rfl) ?_
  intro X Y
  simp only [eqToHom_refl, Category.comp_id]
  rfl

/-- 概要：実現した図式の各頂点は元の豊穣関手の coherent nerve。
方針：実現の評価公式と豊穣後合成の自然性を使う。
規約：関手の空間での厳密な射の等式。
使われ方：比較の列の実際の始点と終点の同定。 -/
lemma KanEnrichedDiagram.realization_evaluate {C : Type (u + 1)} [Category.{u} C]
    [SimplicialCategory C] {J : Type u} [Category.{u} J]
    (D : KanEnrichedDiagram C J) (j : J) :
    D.realization ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex j)) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (D.obj j) := by
  rw [realization, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.kanDiagramRealization_evaluate]
  change _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap D.toEnrichedFunctor ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.kanDiagramEvaluationEnriched j) = _
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap_comp, D.toEnrichedFunctor_evaluate]

/-- 概要：添字の制限と全対象の対角評価は厳密に可換。
方針：二端点の順序で Hom を展開して同じ比較と作用を回収する。
規約：添字関手の単射性は不要。
使われ方：実現の面と退化の整合性。 -/
lemma KanEnrichedDiagram.reindex_diagonal {C : Type v} [Category.{u} C]
    [SimplicialCategory C] {J L I : Type u} [Category.{u} J] [Category.{u} L] [LinearOrder I]
    (D : KanEnrichedDiagram C J) (k : L ⥤ J) (σ : I ⥤ L)
    (T : EnrichedFunctor SSet.{u} (SimplicialThickening I) C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.diagonalKanDiagramEvaluation σ (T.comp SSet (D.reindex k).toEnrichedFunctor) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.diagonalKanDiagramEvaluation (σ ⋙ k) (T.comp SSet D.toEnrichedFunctor) := by
  refine EnrichedFunctor.ext SSet (fun _ ↦ rfl) ?_
  intro i j
  simp only [eqToHom_refl, Category.comp_id]
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro P
  have hij : i.as ≤ j.as := SimplicialThickening.Path.le (P.obj 0)
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.diagonalKanDiagramHom σ
    (T.comp SSet (D.reindex k).toEnrichedFunctor) i j).app n P =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.diagonalKanDiagramHom (σ ⋙ k) (T.comp SSet D.toEnrichedFunctor) i j).app n P
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.diagonalKanDiagramHom_of_le _ _ i j hij,
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.diagonalKanDiagramHom_of_le _ _ i j hij]
  rfl

/-- 概要：任意の添字関手の制限と図式の実現は厳密に可換。
方針：uncurry 後に底と全対象の対角評価の制限公式を使う。
規約：高次の面も退化も同じ等式で扱う。
使われ方：合成三角形の三辺を既存の比較の辺として回収する。 -/
lemma KanEnrichedDiagram.realization_reindex {C : Type (u + 1)} [Category.{u} C]
    [SimplicialCategory C] {J L : Type u} [Category.{u} J] [Category.{u} L]
    (D : KanEnrichedDiagram C J) (k : L ⥤ J) :
    D.realization ≫ (pre ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap k))).app
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} = (D.reindex k).realization := by
  apply uncurry_injective
  rw [uncurry_pre_app]
  simp only [realization, uncurry_natural_left, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.kanDiagramRealization, uncurry_curry]
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨σ, T⟩
  exact (D.reindex_diagonal k (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.kanDiagramSimplexBase σ.down) T).symm

end SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
