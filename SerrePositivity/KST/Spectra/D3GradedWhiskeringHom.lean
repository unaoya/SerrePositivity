module

public import SerrePositivity.KST.Spectra.D3GradedWhiskeringNerve
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.VertexTransport.FunctorIsoTransport

/-!
概要：指定豊穣変換の実現の前後合成を、関手空間の同じ実射の作用へ戻す。
方針：同じ区間族の厳密等式を curry し、指定辺の類を端点表示だけ正規化する。
規約：成分での一致から大域的な関手変換の一致を推論しない。
使われ方：元の右射影・BF 構造の関手同型の指定値の回収。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Spectra

/-- 始終点を等式で正規化しても、同じ一次単体の辺の類は同じ値を持つ。 -/
lemma d3HomMk_heq {X : SSet.{u}} {x y x' y' : X _⦋0⦌}
    (a : SSet.Truncated.Edge (X := (truncation 2).obj X) x y)
    (b : SSet.Truncated.Edge (X := (truncation 2).obj X) x' y')
    (hx : x = x') (hy : y = y') (h : a.edge = b.edge) :
    HEq (SSet.Truncated.HomotopyCategory.homMk a)
      (SSet.Truncated.HomotopyCategory.homMk b) := by
  subst x' y'
  have hab : a = b := SSet.Truncated.Edge.ext h
  subst b
  rfl

/-- 同じ端点表示だけを変更した射の指定値は、任意の関手で写しても保持される。 -/
lemma d3MapHom_heq {V W : Type v} [Category V] [Category W]
    {a b a' b' : V} (f : a ⟶ b) (g : a' ⟶ b') (ha : a = a') (hb : b = b')
    (h : HEq f g) (T : V ⥤ W) : HEq (T.map f) (T.map g) := by
  subst a' b'
  cases eq_of_heq h
  rfl

variable {C D E : Type v} [Category.{u} C] [Category.{u} D] [Category.{u} E]
  [SimplicialCategory C] [SimplicialCategory D] [SimplicialCategory E]

/-- 厳密豊穣関手の端点表示だけを変更した実現は、同じ指定関手辺の類を持つ。 -/
lemma d3GradedHom_ofEq_heq [Quasicategory (SimplicialNerve D)]
    {F G F' G' : EnrichedFunctor SSet.{u} C D}
    (η : GradedNatTrans (Center.ofBraidedObj (𝟙_ SSet.{u})) F G)
    (hf : F = F') (hg : G = G') :
    HEq (d3GradedHom (d3GradedOfEq η hf hg)) (d3GradedHom η) := by
  subst F' G'
  rfl

/-- 端点正規化した厳密変換の後合成は、元の同じ後合成の実現値を保持する。 -/
lemma d3GradedHom_postcomp_ofEq_heq [Quasicategory (SimplicialNerve E)]
    {F G F' G' : EnrichedFunctor SSet.{u} C D}
    (η : GradedNatTrans (Center.ofBraidedObj (𝟙_ SSet.{u})) F G)
    (hf : F = F') (hg : G = G') (K : EnrichedFunctor SSet.{u} D E) :
    HEq (d3GradedHom (d3GradedPostcomp (d3GradedOfEq η hf hg) K))
      (d3GradedHom (d3GradedPostcomp η K)) := by
  subst F' G'
  rfl

/-- 前合成した指定変換の実現は、同じ全関手空間の前合成による作用そのもの。 -/
lemma d3GradedHom_precomp_heq [Quasicategory (SimplicialNerve E)]
    (K : EnrichedFunctor SSet.{u} C D) {F G : EnrichedFunctor SSet.{u} D E}
    (η : GradedNatTrans (Center.ofBraidedObj (𝟙_ SSet.{u})) F G) :
    HEq (d3GradedHom (d3GradedPrecomp K η))
      ((SSet.mapHomotopyCategory ((pre (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap K)).app (SimplicialNerve E))).map
        (d3GradedHom η)) := by
  apply d3HomMk_heq
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (StrictEnrichedTransformation.homotopy _ _
      (d3GradedPrecomp K η)))
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (StrictEnrichedTransformation.homotopy F G η)).map
      ((truncation 2).map ((pre (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap K)).app (SimplicialNerve E))))
    (congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap_comp K F))
    (congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap_comp K G))
  change SSet.yonedaEquiv (curry (StrictEnrichedTransformation.family _ _
    (d3GradedPrecomp K η))) = _
  rw [d3GradedPrecomp_family]
  change SSet.yonedaEquiv (curry ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap K ▷ (Δ[1] : SSet.{max u v})) ≫
    StrictEnrichedTransformation.family F G η)) = _
  rw [← curry_pre_app]
  exact SSet.yonedaEquiv_comp _ _

/-- 後合成した指定変換の実現は、同じ全関手空間の後合成による作用そのもの。 -/
lemma d3GradedHom_postcomp_heq [Quasicategory (SimplicialNerve D)]
    [Quasicategory (SimplicialNerve E)] {F G : EnrichedFunctor SSet.{u} C D}
    (η : GradedNatTrans (Center.ofBraidedObj (𝟙_ SSet.{u})) F G)
    (K : EnrichedFunctor SSet.{u} D E) :
    HEq (d3GradedHom (d3GradedPostcomp η K))
      ((SSet.mapHomotopyCategory ((ihom (SimplicialNerve C)).map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap K))).map
        (d3GradedHom η)) := by
  apply d3HomMk_heq
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (StrictEnrichedTransformation.homotopy _ _
      (d3GradedPostcomp η K)))
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (StrictEnrichedTransformation.homotopy F G η)).map
      ((truncation 2).map ((ihom (SimplicialNerve C)).map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap K))))
    (congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap_comp F K))
    (congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap_comp G K))
  change SSet.yonedaEquiv (curry (StrictEnrichedTransformation.family _ _
    (d3GradedPostcomp η K))) = _
  rw [d3GradedPostcomp_family, curry_natural_right]
  exact SSet.yonedaEquiv_comp _ _

/-- 元の関手同型の前合成の順射を、同じ厳密変換の前合成の実現として回収する。 -/
lemma d3GradedIso_precomp_hom_heq [Quasicategory (SimplicialNerve E)]
    (K : EnrichedFunctor SSet.{u} C D) {F G : EnrichedFunctor SSet.{u} D E}
    (η : GradedNatTrans (Center.ofBraidedObj (𝟙_ SSet.{u})) F G)
    (hη : ∀ X, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge
      (StrictEnrichedTransformation.componentHom F G η X)).toTruncated) :
    HEq (((StrictEnrichedTransformation.functorIso F G η hη).precomp (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap K)).hom)
      (d3GradedHom (d3GradedPrecomp K η)) := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_precomp_hom, d3GradedHom_functorIso]
  exact (d3GradedHom_precomp_heq K η).symm

/-- 元の関手同型の後合成の順射を、同じ厳密変換の後合成の実現として回収する。 -/
lemma d3GradedIso_postcomp_hom_heq [Quasicategory (SimplicialNerve D)]
    [Quasicategory (SimplicialNerve E)] {F G : EnrichedFunctor SSet.{u} C D}
    (η : GradedNatTrans (Center.ofBraidedObj (𝟙_ SSet.{u})) F G)
    (K : EnrichedFunctor SSet.{u} D E)
    (hη : ∀ X, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge
      (StrictEnrichedTransformation.componentHom F G η X)).toTruncated) :
    HEq (((StrictEnrichedTransformation.functorIso F G η hη).postcomp (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap K)).hom)
      (d3GradedHom (d3GradedPostcomp η K)) := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_postcomp_hom, d3GradedHom_functorIso]
  exact (d3GradedHom_postcomp_heq η K).symm

/-- 前後合成を連続しても、元の指定厳密変換の実現を回収する。 -/
lemma d3GradedIso_precomp_postcomp_hom_heq {J : Type v} [Category.{u} J]
    [SimplicialCategory J] [Quasicategory (SimplicialNerve E)]
    [Quasicategory (SimplicialNerve J)]
    (K : EnrichedFunctor SSet.{u} C D) {F G : EnrichedFunctor SSet.{u} D E}
    (η : GradedNatTrans (Center.ofBraidedObj (𝟙_ SSet.{u})) F G)
    (L : EnrichedFunctor SSet.{u} E J)
    (hη : ∀ X, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge
      (StrictEnrichedTransformation.componentHom F G η X)).toTruncated) :
    HEq ((((StrictEnrichedTransformation.functorIso F G η hη).precomp
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap K)).postcomp (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap L)).hom)
      (d3GradedHom (d3GradedPostcomp (d3GradedPrecomp K η) L)) := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_postcomp_hom]
  have h := d3MapHom_heq _ _
    (congrArg (fun a ↦ SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex a))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap_comp K F).symm)
    (congrArg (fun a ↦ SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex a))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap_comp K G).symm)
    (d3GradedIso_precomp_hom_heq K η hη)
    (SSet.mapHomotopyCategory ((ihom (SimplicialNerve C)).map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap L)))
  exact h.trans (d3GradedHom_postcomp_heq (d3GradedPrecomp K η) L).symm

/-- 既存関手同型の端点表示の正規化は、同じ順射の指定値を保持する。 -/
lemma d3FunctorIsoOfEq_hom_heq {A X : SSet.{u}} {f g f' g' : A ⟶ X}
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f g) (hf : f = f') (hg : g = g') :
    HEq (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq e hf hg).hom e.hom := by
  subst f' g'
  rfl

/-- 端点表示を正規化した同じ同型へ前合成しても、順射の指定値を保持する。 -/
lemma d3FunctorIsoOfEq_precomp_hom_heq {A B X : SSet.{u}} {f g f' g' : A ⟶ X}
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f g) (hf : f = f') (hg : g = g') (q : B ⟶ A) :
    HEq ((_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq e hf hg).precomp q).hom (e.precomp q).hom := by
  subst f' g'
  rfl

/-- 端点表示を正規化した同じ同型へ後合成しても、順射の指定値を保持する。 -/
lemma d3FunctorIsoOfEq_postcomp_hom_heq {A X Y : SSet.{u}} {f g f' g' : A ⟶ X}
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f g) (hf : f = f') (hg : g = g') (q : X ⟶ Y) :
    HEq ((_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq e hf hg).postcomp q).hom (e.postcomp q).hom := by
  subst f' g'
  rfl

/-- 端点正規化後の連続した前後合成は、元の指定同型の順射を保持する。 -/
lemma d3FunctorIsoOfEq_precomp_postcomp_hom_heq {A B X Y : SSet.{u}}
    {f g f' g' : A ⟶ X} (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f g) (hf : f = f') (hg : g = g')
    (p : B ⟶ A) (q : X ⟶ Y) :
    HEq (((_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq e hf hg).precomp p).postcomp q).hom
      ((e.precomp p).postcomp q).hom := by
  subst f' g'
  rfl

end SerrePositivity.KST.Spectra
