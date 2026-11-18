module

public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RightKanIndexShapePrism
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.LimitConeExtension
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RightKanTransportComparisonVertex
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.NativePullbackLiftDescent
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.SliceConeFamilyEquivalence
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.VertexTransport.FunctorIsoTransportAlgebra
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.MappingSpaces.FunctorIsoWhiskerComposition
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.MappingSpaces.FunctorIsoWhiskerHom
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHomotopyClasses

/-!
概要：指定された添字の実射で制限した右 Kan 輸送錐の比較。
方針：同じ coslice prism を制限した輸送に貼り、全錐の終点比較を頂点へ射影する。
規約：HTT 5.1.5.6、Kerodon Definition 7.3.1.2（Tag 02Y9）の指定輸送の比較。
使われ方：R04.5 の添字変更に沿う値の計算。
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
open SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries
open SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories
open SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions

private lemma actualIndexPrism_fixed {K C D : SSet.{u}} [Quasicategory C]
    {δ δ' : K ⟶ C} (G : C ⟶ D) (v : C _⦋0⦌)
    (a : rightKanShape δ v ⟶ rightKanShape δ' v)
    (l : FunctorIso (pullback.fst (sliceUnderProjection (SSet.yonedaEquiv.symm v)) δ)
      (a ≫ pullback.fst (sliceUnderProjection (SSet.yonedaEquiv.symm v)) δ')) :
    ∃ Q : join (Δ[0] : SSet.{u}) (rightKanShape δ v) ⊗ (Δ[1] : SSet.{u}) ⟶ D,
       SSet.ι₀ ≫ Q = (rightKanCanonicalCone δ G v).val ∧
       SSet.ι₁ ≫ Q = joinMap (𝟙 (Δ[0] : SSet.{u})) a ≫
         (rightKanCanonicalCone δ' G v).val ∧
       (joinInr (Δ[0] : SSet.{u}) (rightKanShape δ v) ▷ (Δ[1] : SSet.{u})) ≫ Q =
         l.simplicialHomotopy.h ≫ sliceUnderProjection (SSet.yonedaEquiv.symm v) ≫ G ∧
       (joinInl (Δ[0] : SSet.{u}) (rightKanShape δ v) ▷ (Δ[1] : SSet.{u})) ≫ Q =
         fst (Δ[0] : SSet.{u}) (Δ[1] : SSet.{u}) ≫ SSet.yonedaEquiv.symm v ≫ G := by
  letI : Quasicategory (sliceUnder (SSet.yonedaEquiv.symm v)) :=
    quasicategory_of_innerFibration (sliceUnderProjection (SSet.yonedaEquiv.symm v))
  obtain ⟨Q, h₀, h₁, hd, hv⟩ := exists_cosliceHomotopyConePrism v l.simplicialHomotopy G
  refine ⟨Q, h₀, ?_, hd, hv⟩
  rw [h₁, sliceUnderUncurry_precomp, Category.assoc]
  rfl

private def familyHomotopy {A D : SSet.{u}} {F G : A ⟶ D}
    (Q : A ⊗ (Δ[1] : SSet.{u}) ⟶ D) (h₀ : SSet.ι₀ ≫ Q = F)
    (h₁ : SSet.ι₁ ≫ Q = G) : SSet.Homotopy F G where
  h := Q
  h₀ := h₀
  h₁ := h₁
  rel := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    rintro ⟨⟨x, hx⟩, i⟩
    exact False.elim hx

private lemma family_diagram_arrow {J D : SSet.{u}}
    {F G : join (Δ[0] : SSet.{u}) J ⟶ D}
    {F' G' : J ⟶ D} (H : SSet.Homotopy F G)
    (H' : SSet.Homotopy F' G')
    (hd : (joinInr (Δ[0] : SSet.{u}) J ▷ (Δ[1] : SSet.{u})) ≫ H.h = H'.h) :
    Arrow.mk ((hoFunctor.map (coneRestriction J D)).toFunctor.map
      (Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy H))) =
    Arrow.mk (Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy H')) := by
  apply Truncated.HomotopyCategory.congr_arrowMk_homMk
  change SSet.yonedaEquiv (curry H.h ≫
      (pre (joinInr (Δ[0] : SSet.{u}) J)).app D) = SSet.yonedaEquiv (curry H'.h)
  congr 1
  apply uncurry_injective
  rw [uncurry_pre_app, uncurry_curry, uncurry_curry, hd]

private lemma family_apex_arrow {J D : SSet.{u}}
    {F G : join (Δ[0] : SSet.{u}) J ⟶ D}
    (H : SSet.Homotopy F G) (z : (Δ[0] : SSet.{u}) ⟶ D)
    (hv : (joinInl (Δ[0] : SSet.{u}) J ▷ (Δ[1] : SSet.{u})) ≫ H.h =
      fst (Δ[0] : SSet.{u}) (Δ[1] : SSet.{u}) ≫ z) :
    Arrow.mk ((hoFunctor.map (coneApexEvaluation J D)).toFunctor.map
      (Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy H))) =
    Arrow.mk (𝟙 (HomotopyCategory.mk (SSet.yonedaEquiv z))) := by
  let e := (functorEdgeOfSimplicialHomotopy H).map ((truncation 2).map (coneApexEvaluation J D))
  let z₀ := stdSimplex.obj₀Equiv.symm (0 : Fin 1)
  have hz₀ : z₀ = SSet.yonedaEquiv (𝟙 (Δ[0] : SSet.{u})) := by
    apply stdSimplex.obj₀Equiv.injective
    exact (Fin.eq_zero _).symm
  have h := ConcreteCategory.congr_hom (NatTrans.congr_app hv (Opposite.op ⦋1⦌))
    (⟨PinchedHom.constant z₀ 1, SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u}))⟩ :
      ((Δ[0] : SSet.{u}) ⊗ (Δ[1] : SSet.{u})) _⦋1⦌)
  have he : e.edge = (Truncated.Edge.id (X := (truncation 2).obj D) (SSet.yonedaEquiv z)).edge := by
    change H.h.app _ ((joinInl (Δ[0] : SSet.{u}) J).app _ (PinchedHom.constant z₀ 1),
        SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u}))) =
      (Truncated.Edge.id (X := (truncation 2).obj D) (SSet.yonedaEquiv z)).edge
    change H.h.app _ ((joinInl (Δ[0] : SSet.{u}) J).app _ (PinchedHom.constant z₀ 1),
        SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u}))) = z.app _ (PinchedHom.constant z₀ 1) at h
    rw [h, pinchedConstant_map, hz₀, ← SSet.yonedaEquiv_comp, Category.id_comp,
      pinchedConstant_one] <;> rfl
  let i := Truncated.Edge.id (X := (truncation 2).obj D) (SSet.yonedaEquiv z)
  have h₀ := Truncated.HomotopyCategory.congr_arrowMk_homMk e i he
  have h₁ : Truncated.HomotopyCategory.homMk i =
      𝟙 (HomotopyCategory.mk (SSet.yonedaEquiv z)) :=
    Truncated.HomotopyCategory.homMk_id (V := (truncation 2).obj D) _
  exact h₀.trans (congrArg Arrow.mk h₁)

private lemma restrict_family_diagram {J I D : SSet.{u}} {x y : join (Δ[0] : SSet.{u}) I ⟶ D}
    {F G : I ⟶ D} (a : J ⟶ I) (H : SSet.Homotopy x y) (β : SSet.Homotopy F G)
    (hd : (joinInr (Δ[0] : SSet.{u}) I ▷ (Δ[1] : SSet.{u})) ≫ H.h = β.h) :
    (joinInr (Δ[0] : SSet.{u}) J ▷ (Δ[1] : SSet.{u})) ≫
      (functorHomotopyPrecomp H (joinMap (𝟙 (Δ[0] : SSet.{u})) a)).h =
    (functorHomotopyPrecomp β a).h := by
  dsimp only [functorHomotopyPrecomp]
  rw [← Category.assoc, ← comp_whiskerRight, joinInr_joinMap, comp_whiskerRight,
    Category.assoc, hd]

private lemma restrict_family_apex {J I D : SSet.{u}} {x y : join (Δ[0] : SSet.{u}) I ⟶ D}
    (a : J ⟶ I) (H : SSet.Homotopy x y) (z : (Δ[0] : SSet.{u}) ⟶ D)
    (hv : (joinInl (Δ[0] : SSet.{u}) I ▷ (Δ[1] : SSet.{u})) ≫ H.h =
      fst (Δ[0] : SSet.{u}) (Δ[1] : SSet.{u}) ≫ z) :
    (joinInl (Δ[0] : SSet.{u}) J ▷ (Δ[1] : SSet.{u})) ≫
      (functorHomotopyPrecomp H (joinMap (𝟙 (Δ[0] : SSet.{u})) a)).h =
    fst (Δ[0] : SSet.{u}) (Δ[1] : SSet.{u}) ≫ z := by
  dsimp only [functorHomotopyPrecomp]
  rw [← Category.assoc, ← comp_whiskerRight, joinInl_joinMap, Category.id_comp, hv]

private lemma family_cocartesian {J D : SSet.{u}} [Quasicategory D]
    {x y : join (Δ[0] : SSet.{u}) J ⟶ D}
    (H : SSet.Homotopy x y) (z : (Δ[0] : SSet.{u}) ⟶ D)
    (hv : (joinInl (Δ[0] : SSet.{u}) J ▷ (Δ[1] : SSet.{u})) ≫ H.h =
      fst (Δ[0] : SSet.{u}) (Δ[1] : SSet.{u}) ≫ z) :
    HasCocartesianHornLifting (coneRestriction J D) (functorEdgeOfSimplicialHomotopy H) := by
  apply hasCocartesianHornLifting_coneRestriction_of_apex
  obtain ⟨h₀, h₁, h⟩ := (Arrow.mk_eq_mk_iff _ _).1 (family_apex_arrow H z hv)
  change IsIso ((hoFunctor.map (coneApexEvaluation J D)).toFunctor.map
    (Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy H)))
  rw [h]
  infer_instance

set_option backward.isDefEq.respectTransparency.types true in
private lemma slice_iso_from_family {J D : SSet.{u}} [Quasicategory D]
    {p : J ⟶ D} (c d : JoinCone p)
    (i : VertexIso (X := coneFamily p) (coneFamilyVertexEquiv p c) (coneFamilyVertexEquiv p d)) :
    ∃ k : VertexIso (X := sliceOver p) c d,
      Arrow.mk ((hoFunctor.map (sliceOverProjection p)).toFunctor.map k.hom) =
        Arrow.mk ((hoFunctor.map (coneFamilyApex p)).toFunctor.map i.hom) := by
  let S := sliceConeFamilyMap p
  let F := (hoFunctor.map S).toFunctor
  let ff := (isQCatEquivalence_sliceConeFamilyMap p).isFullyFaithful.toHoFullyFaithful
  let hC := congrArg (fun v => (HomotopyCategory.mk v : hoFunctor.obj (coneFamily p)))
    (sliceConeFamilyMap_app_zero p c)
  let hD := congrArg (fun v => (HomotopyCategory.mk v : hoFunctor.obj (coneFamily p)))
    (sliceConeFamilyMap_app_zero p d)
  let j : F.obj (HomotopyCategory.mk c) ≅ F.obj (HomotopyCategory.mk d) :=
    eqToIso hC ≪≫ i ≪≫ (eqToIso hD).symm
  let k : VertexIso (X := sliceOver p) c d := ff.preimageIso j
  refine ⟨k, ?_⟩
  rw [← sliceConeFamilyMap_apex, Functor.map_comp, Cat.Hom.comp_toFunctor]
  change Arrow.mk ((hoFunctor.map (coneFamilyApex p)).toFunctor.map (F.map k.hom)) = _
  rw [show F.map k.hom = j.hom from ff.map_preimage j.hom]
  simp only [j, Iso.trans_hom, eqToIso.hom, Iso.symm_hom, eqToIso.inv, Functor.map_comp,
    eqToHom_map, Category.assoc, Arrow.arrow_mk_eqToHom_comp, Arrow.arrow_mk_comp_eqToHom]

private lemma normalize_fixed_apex {𝒞 : Type u} [Category.{u} 𝒞]
    {A B M Z : 𝒞} (e : A ⟶ B) (f : A ⟶ M) (g : B ⟶ M)
    (he : Arrow.mk e = Arrow.mk (𝟙 Z)) (hf : Arrow.mk f = Arrow.mk (𝟙 Z))
    (h : e ≫ g = f) : Arrow.mk g = Arrow.mk (𝟙 Z) := by
  obtain ⟨ha, hb, h₁⟩ := (Arrow.mk_eq_mk_iff _ _).1 he
  obtain ⟨_, hm, h₂⟩ := (Arrow.mk_eq_mk_iff _ _).1 hf
  subst A B M
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at h₁ h₂
  rw [h₁, h₂, Category.id_comp] at h
  rw [h]

private lemma comp_arrow {T : Type u} [Category.{u} T] {a b c x y z : T}
    (f : a ⟶ b) (g : b ⟶ c) (F : x ⟶ y) (G : y ⟶ z)
    (hf : Arrow.mk f = Arrow.mk F) (hg : Arrow.mk g = Arrow.mk G) :
    Arrow.mk (f ≫ g) = Arrow.mk (F ≫ G) := by
  obtain ⟨ha, hb, hf⟩ := (Arrow.mk_eq_mk_iff _ _).1 hf
  obtain ⟨_, hc, hg⟩ := (Arrow.mk_eq_mk_iff _ _).1 hg
  subst a b c
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at hf hg
  rw [hf, hg]

private lemma iso_hom_arrow {J D : SSet.{u}} {x y x' y' : J ⟶ D}
    (i : FunctorIso x y) (j : FunctorIso x' y')
    (hx : x = x') (hy : y = y') (h : HEq i j) :
    Arrow.mk i.hom = Arrow.mk j.hom := by
  subst x' y'
  rw [eq_of_heq h]

/-- 固定した添字の実射による制限は、元の二つの輸送を頂点が恒等な錐同型で比較する。 -/
@[cite HTT "5.1.5.6" (partial := special)
  "指定右 Kan 輸送を同じ coslice 上の添字の実射と比較する。"]
lemma rightKan_actualIndexArrow_transportConeIso :
∀ {K C D : SSet.{u}} [Quasicategory K] [Quasicategory C] [Quasicategory D]
 {δ δ' : K ⟶ C} (e : FunctorIso δ δ') (O : K ⟶ D) (G : C ⟶ D)
 (β : SSet.Homotopy (δ' ≫ G) O) (v : C _⦋0⦌),
let p := sliceUnderProjection (SSet.yonedaEquiv.symm v)
let b := (e.postcomp G).hom ≫
 Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy β)
∀ (a : rightKanShape δ v ⟶ rightKanShape δ' v)
 (ha : a ≫ rightKanProjection δ' v = rightKanProjection δ v)
 (l : FunctorIso (pullback.fst p δ) (a ≫ pullback.fst p δ'))
 (hl : HEq (l.postcomp p) (e.precomp (rightKanProjection δ v)))
 (s : RightKanConeTransport δ O G (functorHomHomotopy b) v)
 (t : RightKanConeTransport δ' O G β v),
let he : a ≫ rightKanDiagram δ' O v = rightKanDiagram δ O v := by
 dsimp only [rightKanDiagram]; rw [← Category.assoc, ha]
let d := (restrictJoinCone t.cone a).cast he
∃ k : VertexIso (X := sliceOver (rightKanDiagram δ O v)) s.cone d,
 eqToHom (congrArg (fun x => (HomotopyCategory.mk x : hoFunctor.obj D)) s.cone_vertex.symm) ≫
   (hoFunctor.map (sliceOverProjection (rightKanDiagram δ O v))).toFunctor.map k.hom ≫
   eqToHom (congrArg (fun x => (HomotopyCategory.mk x : hoFunctor.obj D))
     ((JoinCone.vertex_cast (restrictJoinCone t.cone a) he).trans
       ((restrictJoinCone_vertex t.cone a).trans t.cone_vertex))) =
   𝟙 (HomotopyCategory.mk (G.app _ v)) := by
  intro K C D hK hC hD δ δ' e O G β v
  dsimp only
  intro a ha l hl s t
  let p := sliceUnderProjection (SSet.yonedaEquiv.symm v)
  letI : Quasicategory (sliceUnder (SSet.yonedaEquiv.symm v)) :=
    quasicategory_of_innerFibration p
  let J := rightKanShape δ v
  let I := rightKanShape δ' v
  let q := rightKanProjection δ v
  let q' := rightKanProjection δ' v
  let A := joinMap (𝟙 (Δ[0] : SSet.{u})) a
  let z := SSet.yonedaEquiv.symm v ≫ G
  let b := (e.postcomp G).hom ≫
    Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy β)
  have hdO : a ≫ rightKanDiagram δ' O v = rightKanDiagram δ O v := by
    dsimp only [rightKanDiagram]
    rw [← Category.assoc, ha]
  let d := (restrictJoinCone t.cone a).cast hdO
  obtain ⟨Q, h₀, h₁, hQd, hQv⟩ := actualIndexPrism_fixed G v a l
  let P := familyHomotopy Q h₀ h₁
  let T := familyHomotopy t.family t.start (show SSet.ι₁ ≫ t.family = t.cone.val from rfl)
  let U := functorHomotopyPrecomp T A
  have apex (δ₀ : K ⟶ C) :
      joinInl (Δ[0] : SSet.{u}) (rightKanShape δ₀ v) ≫ (rightKanCanonicalCone δ₀ G v).val =
        SSet.yonedaEquiv.symm v ≫ G := by
    change joinInl _ _ ≫ (sliceUnderUncurry _ ≫ G) = _
    rw [← Category.assoc, sliceUnderUncurry_fixed]
  let W := functorHomotopyPostcomp (functorHomotopyPostcomp l.simplicialHomotopy p) G
  let V := functorHomotopyPrecomp (functorHomotopyPrecomp β q') a
  have hUd : (joinInr (Δ[0] : SSet.{u}) J ▷ (Δ[1] : SSet.{u})) ≫ U.h = V.h :=
    restrict_family_diagram a T _ t.diagram
  have hUv : (joinInl (Δ[0] : SSet.{u}) J ▷ (Δ[1] : SSet.{u})) ≫ U.h =
      fst (Δ[0] : SSet.{u}) (Δ[1] : SSet.{u}) ≫ z := by
    apply restrict_family_apex
    exact t.fixedVertex.trans (congrArg _ (apex δ'))
  let w := functorEdgeOfSimplicialHomotopy P
  let u := functorEdgeOfSimplicialHomotopy U
  let g := w.comp u
  let j := coneRestriction J D
  let Z := functorVertex (rightKanDiagram δ O v)
  let ini := SSet.yonedaEquiv.symm (functorVertex (rightKanCanonicalCone δ G v).val)
  have hg : HasCocartesianHornLifting j g :=
    hasCocartesianHornLifting_comp j w u (family_cocartesian P z hQv) (family_cocartesian U z hUv)
  have hsZ : j.app _ (functorVertex s.cone.val) = Z := congrArg functorVertex s.cone.property
  have hdZ : j.app _ (functorVertex d.val) = Z := congrArg functorVertex d.property
  let es : Truncated.Edge (X := (truncation 2).obj ((ihom (join Δ[0] J)).obj D))
      (SSet.yonedaEquiv ini) (functorVertex s.cone.val) :=
    ⟨s.edge.edge, s.edge.src_eq.trans (SSet.yonedaEquiv.apply_symm_apply _).symm, s.edge.tgt_eq⟩
  let eg : Truncated.Edge (X := (truncation 2).obj ((ihom (join Δ[0] J)).obj D))
      (SSet.yonedaEquiv ini) (functorVertex d.val) :=
    ⟨g.edge, g.src_eq.trans (SSet.yonedaEquiv.apply_symm_apply _).symm, g.tgt_eq⟩
  have hes : HasCocartesianHornLifting j es :=
    (hasCocartesianHornLifting_congr j (show es.edge = s.edge.edge from rfl)).mpr s.edge_cocartesian
  have heg : HasCocartesianHornLifting j eg :=
    (hasCocartesianHornLifting_congr j (show eg.edge = g.edge from rfl)).mpr hg
  let M := (hoFunctor.map ((pre q).app D)).toFunctor
  let B₁ := ((hoFunctor.map j).toFunctor.map (Truncated.HomotopyCategory.homMk w))
  let B₂ := ((hoFunctor.map j).toFunctor.map (Truncated.HomotopyCategory.homMk u))
  have hwB : Arrow.mk B₁ = Arrow.mk (M.map (e.postcomp G).hom) := by
    refine (family_diagram_arrow P W hQd).trans ?_
    dsimp only [W]
    rw [functorHomotopyPostcomp_hom, functorHomotopyPostcomp_hom,
      functorIso_simplicialHomotopy_hom]
    have hL := functorIso_postcomp_hom l p
    have hLG := functorIso_postcomp_hom (l.postcomp p) G
    have hR := functorIso_precomp_hom (e.postcomp G) q
    have hL' : ((l.postcomp p).postcomp G).hom =
        (hoFunctor.map ((ihom J).map G)).toFunctor.map
          ((hoFunctor.map ((ihom J).map p)).toFunctor.map l.hom) :=
      hLG.trans (congrArg (fun m => (hoFunctor.map ((ihom J).map G)).toFunctor.map m) hL)
    refine (congrArg Arrow.mk hL').symm.trans
      (Eq.trans ?_ (congrArg Arrow.mk hR))
    rw [← functorIso_precomp_postcomp]
    have hsrc : pullback.fst p δ ≫ p = q ≫ δ := pullback.condition
    have htgt : (a ≫ pullback.fst p δ') ≫ p = q ≫ δ' := by
      rw [Category.assoc, pullback.condition, ← Category.assoc]
      exact congrArg (· ≫ δ') ha
    change Arrow.mk (((l.postcomp p).postcomp G).hom) =
      Arrow.mk (((e.precomp q).postcomp G).hom)
    exact iso_hom_arrow _ _ (congrArg (· ≫ G) hsrc) (congrArg (· ≫ G) htgt)
      (functorIso_postcomp_heq_of_heq _ _ hsrc.symm htgt.symm hl G)
  have huB : Arrow.mk B₂ = Arrow.mk (M.map
      (Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy β))) := by
    refine (family_diagram_arrow U V hUd).trans ?_
    have hV : V.h = (functorHomotopyPrecomp β q).h := by
      dsimp only [V, functorHomotopyPrecomp]
      rw [← Category.assoc, ← comp_whiskerRight, ha]
    rw [← functorHomotopyPrecomp_hom]
    exact Truncated.HomotopyCategory.congr_arrowMk_homMk _ _ (congrArg (SSet.yonedaEquiv ∘ curry) hV)
  have hgB : Arrow.mk ((hoFunctor.map j).toFunctor.map (Truncated.HomotopyCategory.homMk g)) =
      Arrow.mk (M.map b) := by
    rw [← Truncated.HomotopyCategory.homMk_comp_homMk (Truncated.Edge.compStruct w u),
      Functor.map_comp, M.map_comp]
    exact comp_arrow B₁ B₂ _ _ hwB huB
  have hsB : Arrow.mk ((hoFunctor.map j).toFunctor.map (Truncated.HomotopyCategory.homMk s.edge)) =
      Arrow.mk (M.map b) := by
    refine (kanFunctorHomCongr_arrow (rightKanCanonicalCone δ G v).property
      s.cone.property _).symm.trans ?_
    rw [s.diagram_hom, functorHomHomotopy_hom]
  have hbase : Truncated.HomotopyCategory.homMk (transportBaseEdge ini j Z es hsZ) =
      Truncated.HomotopyCategory.homMk (transportBaseEdge ini j Z eg hdZ) := by
    apply Arrow.mk_injective _ _
    exact (Truncated.HomotopyCategory.congr_arrowMk_homMk
      (transportBaseEdge ini j Z es hsZ) (s.edge.map ((truncation 2).map j)) rfl).trans
      (hsB.trans (hgB.symm.trans (Truncated.HomotopyCategory.congr_arrowMk_homMk
        (g.map ((truncation 2).map j)) (transportBaseEdge ini j Z eg hdZ) rfl)))
  obtain ⟨x, y, hx, hy, i, hi⟩ :=
    exists_kanTransportEndVertexIso_with_factorization_of_homMk_eq ini j Z es eg hsZ hdZ hes heg hbase
  have hx' : x = coneFamilyVertexEquiv _ s.cone := Subtype.ext hx
  have hy' : y = coneFamilyVertexEquiv _ d := Subtype.ext hy
  subst x y
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at hi
  let Qv := (hoFunctor.map (coneApexEvaluation J D)).toFunctor
  let Inc := (hoFunctor.map (vertexFiberι j Z)).toFunctor
  let ν := Qv.map (Inc.map i.hom)
  have hz : SSet.yonedaEquiv z = G.app _ v := by
    change SSet.yonedaEquiv (SSet.yonedaEquiv.symm v ≫ G) = G.app _ v
    rw [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply]
  have hsA : Arrow.mk (Qv.map (Truncated.HomotopyCategory.homMk es)) =
      Arrow.mk (𝟙 (HomotopyCategory.mk (G.app _ v))) := by
    -- Compare the same underlying edge and use the fixed apex of s.
    refine (Truncated.HomotopyCategory.congr_arrowMk_homMk
      (es.map ((truncation 2).map (coneApexEvaluation J D)))
      (s.edge.map ((truncation 2).map (coneApexEvaluation J D))) rfl).trans ?_
    let S := familyHomotopy s.family s.start (show SSet.ι₁ ≫ s.family = s.cone.val from rfl)
    have h := family_apex_arrow S z (s.fixedVertex.trans
      (congrArg _ (apex δ)))
    rw [hz] at h
    exact h
  have hgA : Arrow.mk (Qv.map (Truncated.HomotopyCategory.homMk eg)) =
      Arrow.mk (𝟙 (HomotopyCategory.mk (G.app _ v))) := by
    refine (Truncated.HomotopyCategory.congr_arrowMk_homMk
      (eg.map ((truncation 2).map (coneApexEvaluation J D)))
      (g.map ((truncation 2).map (coneApexEvaluation J D))) rfl).trans ?_
    change Arrow.mk (Qv.map (Truncated.HomotopyCategory.homMk (w.comp u))) = _
    rw [← Truncated.HomotopyCategory.homMk_comp_homMk (Truncated.Edge.compStruct w u),
      Qv.map_comp]
    have h := comp_arrow _ _ _ _ (family_apex_arrow P z hQv) (family_apex_arrow U z hUv)
    rw [hz, Category.id_comp] at h
    exact h
  have hν := normalize_fixed_apex _ _ ν hsA hgA
    (by simpa only [Qv.map_comp, ν, Inc] using congrArg Qv.map hi)
  obtain ⟨k, hk⟩ := slice_iso_from_family s.cone d i
  refine ⟨k, Arrow.mk_injective _ _ ?_⟩
  simp only [Arrow.arrow_mk_comp_eqToHom, Arrow.arrow_mk_eqToHom_comp]
  rw [hk, coneFamilyApex_eq_evaluation, Functor.map_comp, Cat.Hom.comp_toFunctor]
  exact hν

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions
