module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RightKanTransportCounitRestriction
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.FunctorHomCongrArrow
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.TransportEndIsoFactorization
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianTypedComposition

/-!
概要：元の大域比較のhom_facに沿う指定右Kan輸送の比較を、元の全錐の辺との合成式で取り出す。
方針：標準錐の同じ前合成と既存のcocartesian合成・終点比較を使う。
規約：HTT §4.3.2、Kerodon §7.3（Tag 02Y1）の既存構成の自然性の法則。
使われ方：S8 の元の指定大域比較の成分を、同じ指定極限比較へ戻す証明の分割。
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations
open SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions

/-- 同じ指定余単位との両立を持つ既存の大域比較は、元の輸送辺との因子分解式を与える。 -/
lemma rightKanTransport_comparison_factorization
    {K C D : SSet.{u}} [Quasicategory D] {δ : K ⟶ C} {F₀ : K ⟶ D} {F G : C ⟶ D}
    (α : SSet.Homotopy (δ ≫ F) F₀) (β : SSet.Homotopy (δ ≫ G) F₀)
    (η : FunctorIso F G)
    (hη : rightKanHomMap δ (Truncated.HomotopyCategory.homMk
      (functorEdgeOfSimplicialHomotopy β)) F η.hom =
        Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy α))
    (c : C _⦋0⦌) (t : RightKanConeTransport δ F₀ F α c)
    (s : RightKanConeTransport δ F₀ G β c) :
    ∃ i : VertexIso (coneFamilyVertexEquiv _ t.cone) (coneFamilyVertexEquiv _ s.cone),
      Truncated.HomotopyCategory.homMk t.edge ≫
        (hoFunctor.map (vertexFiberι (coneRestriction (rightKanShape δ c) D)
          (functorVertex (rightKanDiagram δ F₀ c)))).toFunctor.map i.hom =
      (hoFunctor.map ((pre (rightKanCanonicalShape δ c)).app D)).toFunctor.map η.hom ≫
        Truncated.HomotopyCategory.homMk s.edge := by
  let J := rightKanShape δ c
  let p := coneRestriction J D
  let a := SSet.yonedaEquiv.symm (functorVertex (rightKanCanonicalCone δ F c).val)
  let b := functorVertex (rightKanDiagram δ F₀ c)
  let ηq : FunctorIso (rightKanCanonicalCone δ F c).val (rightKanCanonicalCone δ G c).val :=
    η.precomp (rightKanCanonicalShape δ c)
  have hηq : ηq.hom =
      (hoFunctor.map ((pre (rightKanCanonicalShape δ c)).app D)).toFunctor.map η.hom := rfl
  obtain ⟨u, hu⟩ := homotopyCategory_homMk_surjective
    (X := (ihom (SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join Δ[0] J)).obj D)
    (functorVertex (rightKanCanonicalCone δ F c).val)
    (functorVertex (rightKanCanonicalCone δ G c).val) ηq.hom
  have huI : IsInvertibleEdge u := by
    change IsIso (Truncated.HomotopyCategory.homMk u)
    rw [hu]
    infer_instance
  let g := u.comp s.edge
  have hg : HasCocartesianHornLifting p g :=
    hasCocartesianHornLifting_comp p u s.edge (huI.hasCocartesianHornLifting p) s.edge_cocartesian
  have hgclass : Truncated.HomotopyCategory.homMk g =
      (hoFunctor.map ((pre (rightKanCanonicalShape δ c)).app D)).toFunctor.map η.hom ≫
        Truncated.HomotopyCategory.homMk s.edge := by
    rw [← Truncated.HomotopyCategory.homMk_comp_homMk (Truncated.Edge.compStruct u s.edge), hu, hηq]
  let e : Truncated.Edge (X := (truncation 2).obj ((ihom (join Δ[0] J)).obj D))
      (SSet.yonedaEquiv a) (functorVertex t.cone.val) :=
    { edge := t.edge.edge
      src_eq := t.edge.src_eq.trans (SSet.yonedaEquiv.apply_symm_apply _).symm
      tgt_eq := t.edge.tgt_eq }
  let f : Truncated.Edge (X := (truncation 2).obj ((ihom (join Δ[0] J)).obj D))
      (SSet.yonedaEquiv a) (functorVertex s.cone.val) :=
    { edge := g.edge
      src_eq := g.src_eq.trans (SSet.yonedaEquiv.apply_symm_apply _).symm
      tgt_eq := g.tgt_eq }
  have he : HasCocartesianHornLifting p e :=
    (hasCocartesianHornLifting_congr p (show e.edge = t.edge.edge from rfl)).mpr t.edge_cocartesian
  have hf : HasCocartesianHornLifting p f :=
    (hasCocartesianHornLifting_congr p (show f.edge = g.edge from rfl)).mpr hg
  have hy : p.app _ (functorVertex t.cone.val) = b := congrArg functorVertex t.cone.property
  have hz : p.app _ (functorVertex s.cone.val) = b := congrArg functorVertex s.cone.property
  have hgc : kanFunctorHomCongr (rightKanCanonicalCone δ F c).property s.cone.property
      ((hoFunctor.map p).toFunctor.map (Truncated.HomotopyCategory.homMk g)) =
      (hoFunctor.map ((pre (rightKanProjection δ c)).app D)).toFunctor.map
        (Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy α)) := by
    rw [hgclass]
    exact rightKanTransport_counit_restriction α β η.hom hη c s
  have hbase : Truncated.HomotopyCategory.homMk (transportBaseEdge a p b e hy) =
      Truncated.HomotopyCategory.homMk (transportBaseEdge a p b f hz) := by
    apply Arrow.mk_injective _ _
    calc
      _ = Arrow.mk ((hoFunctor.map p).toFunctor.map (Truncated.HomotopyCategory.homMk t.edge)) :=
        Truncated.HomotopyCategory.congr_arrowMk_homMk
          (transportBaseEdge a p b e hy) (t.edge.map ((truncation 2).map p)) rfl
      _ = Arrow.mk (kanFunctorHomCongr (rightKanCanonicalCone δ F c).property t.cone.property
          ((hoFunctor.map p).toFunctor.map (Truncated.HomotopyCategory.homMk t.edge))) :=
        (kanFunctorHomCongr_arrow (rightKanCanonicalCone δ F c).property t.cone.property
          ((hoFunctor.map p).toFunctor.map (Truncated.HomotopyCategory.homMk t.edge))).symm
      _ = Arrow.mk ((hoFunctor.map ((pre (rightKanProjection δ c)).app D)).toFunctor.map
          (Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy α))) :=
        congrArg Arrow.mk t.diagram_hom
      _ = Arrow.mk (kanFunctorHomCongr (rightKanCanonicalCone δ F c).property s.cone.property
          ((hoFunctor.map p).toFunctor.map (Truncated.HomotopyCategory.homMk g))) :=
        (congrArg Arrow.mk hgc).symm
      _ = Arrow.mk ((hoFunctor.map p).toFunctor.map (Truncated.HomotopyCategory.homMk g)) :=
        kanFunctorHomCongr_arrow (rightKanCanonicalCone δ F c).property s.cone.property
          ((hoFunctor.map p).toFunctor.map (Truncated.HomotopyCategory.homMk g))
      _ = _ := Truncated.HomotopyCategory.congr_arrowMk_homMk
          (g.map ((truncation 2).map p)) (transportBaseEdge a p b f hz) rfl
  obtain ⟨v, w, hv, hw, i, hi⟩ :=
    exists_kanTransportEndVertexIso_with_factorization_of_homMk_eq a p b e f hy hz he hf hbase
  have hv' : v = coneFamilyVertexEquiv _ t.cone := Subtype.ext hv
  have hw' : w = coneFamilyVertexEquiv _ s.cone := Subtype.ext hw
  subst v w
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at hi
  have hx := SSet.yonedaEquiv.apply_symm_apply (functorVertex (rightKanCanonicalCone δ F c).val)
  have het := homMk_transport hx rfl e t.edge rfl
  have hft := homMk_transport hx rfl f g rfl
  have he' : Truncated.HomotopyCategory.homMk e =
      eqToHom (congrArg HomotopyCategory.mk hx) ≫ Truncated.HomotopyCategory.homMk t.edge := by
    rw [← het]
    simp only [eqToHom_trans_assoc, eqToHom_refl, Category.id_comp, Category.comp_id]
  have hf' : Truncated.HomotopyCategory.homMk f =
      eqToHom (congrArg HomotopyCategory.mk hx) ≫ Truncated.HomotopyCategory.homMk g := by
    rw [← hft]
    simp only [eqToHom_trans_assoc, eqToHom_refl, Category.id_comp, Category.comp_id]
  refine ⟨i, ?_⟩
  rw [← hgclass]
  apply (cancel_epi (eqToHom (congrArg HomotopyCategory.mk hx))).mp
  simpa only [he', hf', Category.assoc] using hi

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions
