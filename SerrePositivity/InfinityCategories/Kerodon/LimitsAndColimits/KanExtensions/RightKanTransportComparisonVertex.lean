module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RightKanTransportComparisonFactorization
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RightKanCanonicalHomEvaluation
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RightKanTransportApexHom
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.LimitConeFamilyProjectionArrow
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.ConeFamilyApexEvaluation

/-!
概要：同じ指定余単位を保つ元の大域比較の成分は、同じ指定輸送錐の標準極限比較である。
方針：既存の輸送の因子分解式を頂点へ射影し、元の定値頂点射と標準形状の評価則で正規化する。
規約：HTT §4.3.2、Kerodon §7.3（Tag 02Y1）の既存Kan比較の自然性の法則。
使われ方：S8 の固定された値比較を、既存の全関手の比較に沿って照合する。
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
open SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions

private lemma normalize_apex_square {𝒞 : Type v} [Category.{w} 𝒞]
    {A B M N V W : 𝒞} (f : A ⟶ B) (g : M ⟶ N) (ν : A ⟶ M) (μ : B ⟶ N)
    (a : A ≅ V) (b : B ≅ V) (c : M ≅ W) (d : N ≅ W)
    (hf : f ≫ b.hom = a.hom) (hg : g ≫ d.hom = c.hom) (h : f ≫ μ = ν ≫ g) :
    b.inv ≫ μ ≫ d.hom = a.inv ≫ ν ≫ c.hom := by
  apply (cancel_epi a.hom).mp
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [← hf]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [← Category.assoc, h, Category.assoc, hg]

/-- 元の指定余単位に両立する大域比較の成分と、指定輸送錐の標準極限比較は一致する。 -/
lemma rightKanTransport_comparison_vertex
    {K C D : SSet.{u}} [Quasicategory D] {δ : K ⟶ C} {F₀ : K ⟶ D} {F G : C ⟶ D}
    (α : SSet.Homotopy (δ ≫ F) F₀) (β : SSet.Homotopy (δ ≫ G) F₀)
    (η : FunctorIso F G)
    (hη : rightKanHomMap δ (Truncated.HomotopyCategory.homMk
      (functorEdgeOfSimplicialHomotopy β)) F η.hom =
        Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy α))
    (c : C _⦋0⦌) (t : RightKanConeTransport δ F₀ F α c)
    (s : RightKanConeTransport δ F₀ G β c) (ht : IsLimitCone t.cone) (hs : IsLimitCone s.cone) :
    eqToHom (congrArg (fun x => (HomotopyCategory.mk x : hoFunctor.obj D)) t.cone_vertex.symm) ≫
      (limitVertexIso t.cone s.cone ht hs).hom ≫
        eqToHom (congrArg (fun x => (HomotopyCategory.mk x : hoFunctor.obj D)) s.cone_vertex) =
      functorHomEvaluate η.hom c := by
  obtain ⟨i, hi⟩ := rightKanTransport_comparison_factorization α β η hη c t s
  let J := rightKanShape δ c
  let Q := coneApexEvaluation J D
  let I := SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι
    (coneRestriction J D) (functorVertex (rightKanDiagram δ F₀ c))
  let μ := (hoFunctor.map Q).toFunctor.map ((hoFunctor.map I).toFunctor.map i.hom)
  let ν := (hoFunctor.map Q).toFunctor.map
    ((hoFunctor.map ((pre (rightKanCanonicalShape δ c)).app D)).toFunctor.map η.hom)
  let eF0 := eqToIso (congrArg (fun x => (HomotopyCategory.mk x : hoFunctor.obj D))
    ((coneApexEvaluation_vertex (rightKanCanonicalCone δ F c)).trans
      (rightKanCanonicalCone_vertex δ F c)))
  let eF1 := eqToIso (congrArg (fun x => (HomotopyCategory.mk x : hoFunctor.obj D))
    ((coneApexEvaluation_vertex t.cone).trans t.cone_vertex))
  let eG0 := eqToIso (congrArg (fun x => (HomotopyCategory.mk x : hoFunctor.obj D))
    ((coneApexEvaluation_vertex (rightKanCanonicalCone δ G c)).trans
      (rightKanCanonicalCone_vertex δ G c)))
  let eG1 := eqToIso (congrArg (fun x => (HomotopyCategory.mk x : hoFunctor.obj D))
    ((coneApexEvaluation_vertex s.cone).trans s.cone_vertex))
  have hmap : (hoFunctor.map Q).toFunctor.map (Truncated.HomotopyCategory.homMk t.edge) ≫ μ =
      ν ≫ (hoFunctor.map Q).toFunctor.map (Truncated.HomotopyCategory.homMk s.edge) := by
    have h := congrArg (hoFunctor.map Q).toFunctor.map hi
    simpa only [Functor.map_comp] using h
  have hμ : eF1.inv ≫ μ ≫ eG1.hom = eF0.inv ≫ ν ≫ eG0.hom :=
    normalize_apex_square _ _ ν μ eF0 eF1 eG0 eG1 t.apex_hom s.apex_hom hmap
  have hν : eF0.inv ≫ ν ≫ eG0.hom = functorHomEvaluate η.hom c := by
    apply (cancel_epi eF0.hom).mp
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    let z := (joinInl (Δ[0] : SSet.{u}) J).app _ (stdSimplex.obj₀Equiv.symm 0)
    have h := rightKanCanonicalShape_hom_apex δ c η.hom
    have h0 := congrArg (fun m =>
      eqToHom (congrArg (fun x => (HomotopyCategory.mk x : hoFunctor.obj D))
        (evaluateFunctorAt_functorVertex z (rightKanCanonicalShape δ c ≫ F))) ≫ m) h
    simp only [functorHomEvaluate, Category.assoc, eqToHom_trans_assoc, eqToHom_refl,
      Category.id_comp] at h0
    simpa only [eF0, eG0, ν, Q, coneApexEvaluation, functorHomEvaluate, eqToIso.hom,
      Category.assoc, eqToHom_trans_assoc, eqToHom_trans, eqToHom_refl,
      Category.id_comp, Category.comp_id] using h0
  apply Arrow.mk_injective _ _
  calc
    _ = Arrow.mk (limitVertexIso t.cone s.cone ht hs).hom := by
      simp only [Arrow.arrow_mk_comp_eqToHom, Arrow.arrow_mk_eqToHom_comp]
    _ = Arrow.mk ((hoFunctor.map (coneFamilyApex (rightKanDiagram δ F₀ c))).toFunctor.map i.hom) :=
      (limitVertexIso_coneFamily_arrow t.cone s.cone ht hs i.hom).symm
    _ = Arrow.mk μ := by
      rw [coneFamilyApex_eq_evaluation, Functor.map_comp, Cat.Hom.comp_toFunctor]
      rfl
    _ = Arrow.mk (eF1.inv ≫ μ ≫ eG1.hom) := by
      simp only [eF1, eG1, eqToIso.inv, eqToIso.hom,
        Arrow.arrow_mk_comp_eqToHom, Arrow.arrow_mk_eqToHom_comp]
    _ = _ := congrArg Arrow.mk (hμ.trans hν)

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions
