module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.FunctorComparisons.DGStrictFunctorNerveComponents
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.IntervalFunctorHom
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHomCorrespondence
/-!
概要：元の厳密変換の指定ホモトピーの類は、実合成二単体により恒等・合成を保つ。
方針：元の全閉零成分と全 Hom 自然性、実 nerve 写像と端点輸送を使う。
規約：関手圏の射の等式を実単体で証明する。使われ方：kernel 比較の coherence。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet MonoidalCategory MonoidalClosed
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (C E : Type v)
  [_root_.SerrePositivity.DifferentialGraded.DGCategory R C] [_root_.SerrePositivity.DifferentialGraded.DGCategory R E]
/-- 実関手圏写像の同じ頂点公式による、元の対象の指定同型。 -/
def dgStrictFunctorNerveVertexIso (F : _root_.SerrePositivity.DifferentialGraded.DGFunctor R C E) :
    (HomotopyCategory.mk ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictFunctorNerveMap R C E).app (Opposite.op ⦋0⦌)
      (ComposableArrows.mk₀ (⟨F⟩ : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGStrictFunctor R C E))) :
        hoFunctor.obj ((ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R C)).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R E))) ≅
      HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map F)) :=
  eqToIso (congrArg HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictFunctorNerveMap_vertex R C E F))
/-- 元の変換の実 nerve 辺を同じ関手頂点へ輸送した h Fun の射。 -/
def dgStrictNatTransNerveHom {F G : DGFunctor R C E} (η : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans F G) :
    _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map F) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map G) :=
  (dgStrictFunctorNerveVertexIso R C E F).inv ≫
    HomotopyCategory.homMk
      ((nerve.edgeMk (show (⟨F⟩ : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGStrictFunctor R C E) ⟶ ⟨G⟩ from η)).map
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictFunctorNerveMap R C E)) ≫ (dgStrictFunctorNerveVertexIso R C E G).hom
/-- 元の変換の実 nerve 像は、元の指定ホモトピーの辺の類そのもの。 -/
lemma dgStrictNatTransNerveHom_spec {F G : DGFunctor R C E} (η : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans F G) :
    dgStrictNatTransNerveHom R C E η =
      Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy η.homotopy) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.homMk_transport (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictFunctorNerveMap_vertex R C E F)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictFunctorNerveMap_vertex R C E G)
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictFunctorNerveMap_edge R C E η
/-- 同じ実 nerve 像は、元の厳密恒等変換を恒等射へ送る。 -/
lemma dgStrictNatTransNerveHom_id (F : _root_.SerrePositivity.DifferentialGraded.DGFunctor R C E) :
    dgStrictNatTransNerveHom R C E (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransId F) =
      𝟙 (HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map F))) := by
  change (dgStrictFunctorNerveVertexIso R C E F).inv ≫
      HomotopyCategory.homMk
        ((nerve.edgeMk (𝟙 (⟨F⟩ : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGStrictFunctor R C E))).map
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictFunctorNerveMap R C E)) ≫ (dgStrictFunctorNerveVertexIso R C E F).hom = _
  rw [nerve.edgeMk_id, SSet.Edge.map_id]
  erw [HomotopyCategory.homMk_id]
  rw [Category.id_comp]
  exact (dgStrictFunctorNerveVertexIso R C E F).inv_hom_id
/-- 同じ実 nerve 像は、元の通常順合成を h Fun の合成へ送る。 -/
lemma dgStrictNatTransNerveHom_comp {F G H : _root_.SerrePositivity.DifferentialGraded.DGFunctor R C E}
    (η : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans F G) (θ : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans G H) :
    dgStrictNatTransNerveHom R C E (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransComp η θ) =
      dgStrictNatTransNerveHom R C E η ≫ dgStrictNatTransNerveHom R C E θ := by
  let a : (⟨F⟩ : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGStrictFunctor R C E) ⟶ ⟨G⟩ := η
  let b : (⟨G⟩ : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGStrictFunctor R C E) ⟶ ⟨H⟩ := θ
  obtain ⟨t⟩ := (nerve.nonempty_compStruct_iff a b (a ≫ b)).2 rfl
  have ht := HomotopyCategory.homMk_comp_homMk (t.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictFunctorNerveMap R C E))
  simp only [dgStrictNatTransNerveHom, Category.assoc, Iso.hom_inv_id_assoc]
  have he := congrArg (fun m => (dgStrictFunctorNerveVertexIso R C E F).inv ≫ m ≫
    (dgStrictFunctorNerveVertexIso R C E H).hom) ht.symm
  simpa only [Category.assoc] using! he
/-- 元の指定恒等ホモトピーの辺の類は、元の関手圏の恒等射。 -/
lemma dgStrictNatTrans_homotopyHom_id (F : _root_.SerrePositivity.DifferentialGraded.DGFunctor R C E) :
    Truncated.HomotopyCategory.homMk
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransId F).homotopy) =
      𝟙 (HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map F))) := by
  simpa only [dgStrictNatTransNerveHom_spec] using dgStrictNatTransNerveHom_id R C E F
/-- 元の指定合成ホモトピーの辺の類は、元の二変換の類の合成。 -/
lemma dgStrictNatTrans_homotopyHom_comp {F G H : _root_.SerrePositivity.DifferentialGraded.DGFunctor R C E}
    (η : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans F G) (θ : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans G H) :
    Truncated.HomotopyCategory.homMk
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransComp η θ).homotopy) =
      Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy η.homotopy) ≫
        Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy θ.homotopy) := by
  simpa only [dgStrictNatTransNerveHom_spec] using dgStrictNatTransNerveHom_comp R C E η θ
/-- 元の dg 関手と全 Hom 自然な厳密変換を、その実 dg nerve 間の h Fun へ送る関手。 -/
def dgStrictFunctorHomFunctor :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGStrictFunctor R C E ⥤ hoFunctor.obj ((ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R C)).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R E)) where
  obj F := HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map F.toDGFunctor))
  map η := dgStrictNatTransNerveHom R C E η
  map_id F := dgStrictNatTransNerveHom_id R C E F.toDGFunctor
  map_comp η θ := dgStrictNatTransNerveHom_comp R C E η θ
end SerrePositivity.InfinityCategories.Project.DerivedCategories
