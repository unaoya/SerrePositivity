module
public import SerrePositivity.InfinityCategories.Derived.DGStrictFunctorNerveComponents
public import SerrePositivity.InfinityCategories.F1B.MappingSpaces.IntervalFunctorHom
public import SerrePositivity.InfinityCategories.F1B.FunctorCategories.FunctorHomCorrespondence
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
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet MonoidalCategory MonoidalClosed
open scoped Simplicial
variable (R : Type u) [CommRing R] (C E : Type v)
  [DGCategory R C] [DGCategory R E]
/-- 実関手圏写像の同じ頂点公式による、元の対象の指定同型。 -/
def dgStrictFunctorNerveVertexIso (F : DGFunctor R C E) :
    (HomotopyCategory.mk ((dgStrictFunctorNerveMap R C E).app (Opposite.op ⦋0⦌)
      (ComposableArrows.mk₀ (⟨F⟩ : DGStrictFunctor R C E))) :
        hoFunctor.obj ((ihom (dgNerve R C)).obj (dgNerve R E))) ≅
      HomotopyCategory.mk (functorVertex (dgNerve.map F)) :=
  eqToIso (congrArg HomotopyCategory.mk (dgStrictFunctorNerveMap_vertex R C E F))
/-- 元の変換の実 nerve 辺を同じ関手頂点へ輸送した h Fun の射。 -/
def dgStrictNatTransNerveHom {F G : DGFunctor R C E} (η : StrictNatTrans F G) :
    FunctorHom (dgNerve.map F) (dgNerve.map G) :=
  (dgStrictFunctorNerveVertexIso R C E F).inv ≫
    HomotopyCategory.homMk
      ((nerve.edgeMk (show (⟨F⟩ : DGStrictFunctor R C E) ⟶ ⟨G⟩ from η)).map
        (dgStrictFunctorNerveMap R C E)) ≫ (dgStrictFunctorNerveVertexIso R C E G).hom
/-- 元の変換の実 nerve 像は、元の指定ホモトピーの辺の類そのもの。 -/
lemma dgStrictNatTransNerveHom_spec {F G : DGFunctor R C E} (η : StrictNatTrans F G) :
    dgStrictNatTransNerveHom R C E η =
      Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy η.homotopy) := by
  apply homMk_transport (dgStrictFunctorNerveMap_vertex R C E F)
    (dgStrictFunctorNerveMap_vertex R C E G)
  exact dgStrictFunctorNerveMap_edge R C E η
/-- 同じ実 nerve 像は、元の厳密恒等変換を恒等射へ送る。 -/
lemma dgStrictNatTransNerveHom_id (F : DGFunctor R C E) :
    dgStrictNatTransNerveHom R C E (dgStrictNatTransId F) =
      𝟙 (HomotopyCategory.mk (functorVertex (dgNerve.map F))) := by
  change (dgStrictFunctorNerveVertexIso R C E F).inv ≫
      HomotopyCategory.homMk
        ((nerve.edgeMk (𝟙 (⟨F⟩ : DGStrictFunctor R C E))).map
          (dgStrictFunctorNerveMap R C E)) ≫ (dgStrictFunctorNerveVertexIso R C E F).hom = _
  rw [nerve.edgeMk_id, SSet.Edge.map_id]
  erw [HomotopyCategory.homMk_id]
  rw [Category.id_comp]
  exact (dgStrictFunctorNerveVertexIso R C E F).inv_hom_id
/-- 同じ実 nerve 像は、元の通常順合成を h Fun の合成へ送る。 -/
lemma dgStrictNatTransNerveHom_comp {F G H : DGFunctor R C E}
    (η : StrictNatTrans F G) (θ : StrictNatTrans G H) :
    dgStrictNatTransNerveHom R C E (dgStrictNatTransComp η θ) =
      dgStrictNatTransNerveHom R C E η ≫ dgStrictNatTransNerveHom R C E θ := by
  let a : (⟨F⟩ : DGStrictFunctor R C E) ⟶ ⟨G⟩ := η
  let b : (⟨G⟩ : DGStrictFunctor R C E) ⟶ ⟨H⟩ := θ
  obtain ⟨t⟩ := (nerve.nonempty_compStruct_iff a b (a ≫ b)).2 rfl
  have ht := HomotopyCategory.homMk_comp_homMk (t.map (dgStrictFunctorNerveMap R C E))
  simp only [dgStrictNatTransNerveHom, Category.assoc, Iso.hom_inv_id_assoc]
  have he := congrArg (fun m => (dgStrictFunctorNerveVertexIso R C E F).inv ≫ m ≫
    (dgStrictFunctorNerveVertexIso R C E H).hom) ht.symm
  simpa only [Category.assoc] using! he
/-- 元の指定恒等ホモトピーの辺の類は、元の関手圏の恒等射。 -/
lemma dgStrictNatTrans_homotopyHom_id (F : DGFunctor R C E) :
    Truncated.HomotopyCategory.homMk
        (functorEdgeOfSimplicialHomotopy (dgStrictNatTransId F).homotopy) =
      𝟙 (HomotopyCategory.mk (functorVertex (dgNerve.map F))) := by
  simpa only [dgStrictNatTransNerveHom_spec] using dgStrictNatTransNerveHom_id R C E F
/-- 元の指定合成ホモトピーの辺の類は、元の二変換の類の合成。 -/
lemma dgStrictNatTrans_homotopyHom_comp {F G H : DGFunctor R C E}
    (η : StrictNatTrans F G) (θ : StrictNatTrans G H) :
    Truncated.HomotopyCategory.homMk
        (functorEdgeOfSimplicialHomotopy (dgStrictNatTransComp η θ).homotopy) =
      Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy η.homotopy) ≫
        Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy θ.homotopy) := by
  simpa only [dgStrictNatTransNerveHom_spec] using dgStrictNatTransNerveHom_comp R C E η θ
/-- 元の dg 関手と全 Hom 自然な厳密変換を、その実 dg nerve 間の h Fun へ送る関手。 -/
def dgStrictFunctorHomFunctor :
    DGStrictFunctor R C E ⥤ hoFunctor.obj ((ihom (dgNerve R C)).obj (dgNerve R E)) where
  obj F := HomotopyCategory.mk (functorVertex (dgNerve.map F.toDGFunctor))
  map η := dgStrictNatTransNerveHom R C E η
  map_id F := dgStrictNatTransNerveHom_id R C E F.toDGFunctor
  map_comp η θ := dgStrictNatTransNerveHom_comp R C E η θ
end SerrePositivity.InfinityCategories
