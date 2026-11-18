module

public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.MappingSpaces.FunctorIsoWhiskerHom
public import SerrePositivity.InfinityCategories.Sheaves.RightKanCounitAtApex
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RightKanCanonicalIndexPrism
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.FunctorHomCongrArrow
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.RelativeFunctorVertexIsoProjection
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.HomotopyRepresentative

/-!
概要：指定始点の下で同じ底に写る相対同型は、指定頂点での錐の余単位を保つ。
方針：指定した辺と添字の座標に既存の評価則を適用する。
使われ方：離散前層の重み付き切断の自然性。
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations
open SerrePositivity.InfinityCategories.Sheaves
open SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
open SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
open SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories
open SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy

namespace SerrePositivity.InfinityCategories.Sheaves

private lemma mapArrow_eq_id_of_postcomp
    {J K X : SSet.{u}} {f g : J ⟶ K} (i : FunctorIso f g)
    (p : K ⟶ X) {D : J ⟶ X} (hf : f ≫ p = D) (hg : g ≫ p = D)
    (h : i.postcomp p = eqToIso (congrArg (fun v : J ⟶ X =>
      HomotopyCategory.mk (functorVertex v)) (hf.trans hg.symm))) :
    Arrow.mk ((hoFunctor.map ((ihom J).map p)).toFunctor.map i.hom) =
      Arrow.mk (𝟙 (HomotopyCategory.mk (functorVertex D))) := by
  have h₁ := functorIso_postcomp_hom i p
  have h₂ := congrArg Iso.hom h
  rw [h₁] at h₂
  apply (congrArg Arrow.mk h₂).trans
  apply (Arrow.mk_eq_mk_iff _ _).2
  refine ⟨congrArg (fun v => HomotopyCategory.mk (functorVertex v)) hf,
    congrArg (fun v => HomotopyCategory.mk (functorVertex v)) hg, ?_⟩
  simp only [eqToIso.hom, Category.id_comp, eqToHom_trans]

private lemma normalize_arrow {T : Type u} [Category T] {a b x y : T}
    (f : a ⟶ b) (g : x ⟶ y) (hx : a = x) (hy : b = y) (h : Arrow.mk f = Arrow.mk g) :
    eqToHom hx.symm ≫ f ≫ eqToHom hy = g := by
  subst x y
  simpa only [eqToHom_refl, Category.id_comp, Category.comp_id] using Arrow.mk_injective _ _ h

private lemma fixedConeApexHom_arrow {J D : SSet.{u}} {p : J ⟶ D}
    (c d : JoinCone p) (H : SSet.Homotopy c.val d.val) (z : (Δ[0] : SSet.{u}) ⟶ D)
    (h : (joinInl (Δ[0] : SSet.{u}) J ▷ (Δ[1] : SSet.{u})) ≫ H.h =
      fst (Δ[0] : SSet.{u}) (Δ[1] : SSet.{u}) ≫ z) :
    Arrow.mk (functorHomEvaluate
      (Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy H))
      (SSet.yonedaEquiv (joinInl (Δ[0] : SSet.{u}) J))) =
    Arrow.mk (𝟙 (HomotopyCategory.mk (SSet.yonedaEquiv z))) := by
  rw [functorHomEvaluate_homotopy]
  let t := homotopyIntervalEdge.edge
  let r := SSet.yonedaEquiv (𝟙 (Δ[0] : SSet.{u}))
  let x := SSet.yonedaEquiv (joinInl (Δ[0] : SSet.{u}) J)
  let e := Truncated.Edge.id (X := (truncation 2).obj D) (SSet.yonedaEquiv z)
  refine (Truncated.HomotopyCategory.congr_arrowMk_homMk _ e ?_).trans
    (congrArg Arrow.mk (Truncated.HomotopyCategory.homMk_id (V := (truncation 2).obj D) _))
  change H.h.app _ ((Truncated.Edge.id (X := (truncation 2).obj (join Δ[0] J)) x).edge, t) =
    e.edge
  rw [← pinchedConstant_one x, show x = (joinInl Δ[0] J).app _ r by
    dsimp only [x, r]; rw [← SSet.yonedaEquiv_comp, Category.id_comp], ← pinchedConstant_map]
  have hh := congrArg (fun q : (Δ[0] : SSet.{u}) ⊗ Δ[1] ⟶ D =>
    q.app (Opposite.op ⦋1⦌) (Basic.PinchedHom.constant r 1, t)) h
  refine hh.trans ?_
  change z.app _ (Basic.PinchedHom.constant r 1) = e.edge
  rw [pinchedConstant_map, show z.app _ r = SSet.yonedaEquiv z by
    dsimp only [r]; rw [← SSet.yonedaEquiv_comp, Category.id_comp], pinchedConstant_one]
  rfl

private lemma coneCounitAtApex_of_fixedApex {J D : SSet.{u}} [Quasicategory D]
    {p : J ⟶ D} (c d : JoinCone p) (m : FunctorHom c.val d.val)
    (v : D _⦋0⦌) (hc : c.vertex = v) (hd : d.vertex = v)
    (ha : Arrow.mk (functorHomEvaluate m (SSet.yonedaEquiv (joinInl (Δ[0] : SSet.{u}) J))) =
        Arrow.mk (𝟙 (HomotopyCategory.mk v)))
    (hb : kanFunctorHomCongr c.property d.property
      ((hoFunctor.map ((pre (joinInr (Δ[0] : SSet.{u}) J)).app D)).toFunctor.map m) = 𝟙 _) :
    coneCounitAtApex c hc = coneCounitAtApex d hd := by
  let a : (HomotopyCategory.mk c.vertex : hoFunctor.obj D) ⟶ HomotopyCategory.mk d.vertex :=
    functorHomEvaluate m (SSet.yonedaEquiv (joinInl (Δ[0] : SSet.{u}) J))
  have ha' := normalize_arrow a (𝟙 _) (congrArg HomotopyCategory.mk hc)
    (congrArg HomotopyCategory.mk hd) ha
  have hn := coneCounitHom_morphism_naturality c d m
  have hn' : constantFunctorHomMap J a ≫ coneCounitHom d = coneCounitHom c :=
    hn.trans (by rw [hb, Category.comp_id])
  change constantFunctorHomMap J (eqToHom (congrArg HomotopyCategory.mk hc).symm) ≫
    coneCounitHom c =
      constantFunctorHomMap J (eqToHom (congrArg HomotopyCategory.mk hd).symm) ≫ coneCounitHom d
  rw [← hn', ← Category.assoc, ← constantFunctorHomMap_comp]
  have he : eqToHom (congrArg HomotopyCategory.mk hc).symm ≫ a =
      eqToHom (congrArg HomotopyCategory.mk hd).symm :=
    (cancel_mono (eqToHom (congrArg HomotopyCategory.mk hd))).mp (by
      rw [Category.assoc, ha', eqToHom_trans]
      exact (eqToHom_refl _ _).symm)
  rw [he]

/-- 共通の底へ写る coslice の射が定める錐。 -/
def coneOfCosliceMap {J X D : SSet.{u}} {v : X _⦋0⦌}
    (f : J ⟶ sliceUnder (SSet.yonedaEquiv.symm v)) (G : X ⟶ D)
    {p : J ⟶ D} (h : f ≫ sliceUnderProjection (SSet.yonedaEquiv.symm v) ≫ G = p) :
    JoinCone p :=
  ⟨sliceUnderUncurry f ≫ G, by rw [← Category.assoc, sliceUnderUncurry_projection]; exact h⟩

/-- 同じ錐の頂点は元の指定始点の像。 -/
lemma coneOfCosliceMap_atApex {J X D : SSet.{u}} {v : X _⦋0⦌}
    (f : J ⟶ sliceUnder (SSet.yonedaEquiv.symm v)) (G : X ⟶ D)
    {p : J ⟶ D} (h : f ≫ sliceUnderProjection (SSet.yonedaEquiv.symm v) ≫ G = p) :
    (coneOfCosliceMap f G h).vertex = G.app (Opposite.op ⦋0⦌) v := by
  rw [JoinCone.vertex_eq]
  change SSet.yonedaEquiv (joinInl Δ[0] J ≫ sliceUnderUncurry f ≫ G) = _
  rw [← Category.assoc, sliceUnderUncurry_fixed, SSet.yonedaEquiv_comp, Equiv.apply_symm_apply]

/-- 指定始点の下で同じ底に写る相対同型は、指定頂点での錐の余単位を保つ。
Kerodon §4.6.6（Tag 04J1）の区間と join の比較。HTT 5.1.5.6 で使う形状照合。 -/
lemma coneOfCosliceMap_counit_relativeIso
    {J X D : SSet.{u}} [Quasicategory X] [Quasicategory D]
    (v : X _⦋0⦌) (G : X ⟶ D)
    {a : J ⟶ X} (f g : J ⟶ sliceUnder (SSet.yonedaEquiv.symm v))
    (hf : f ≫ sliceUnderProjection (SSet.yonedaEquiv.symm v) = a)
    (hg : g ≫ sliceUnderProjection (SSet.yonedaEquiv.symm v) = a)
    (i : VertexIso
      (relativeFunctorVertex (sliceUnderProjection (SSet.yonedaEquiv.symm v)) a f hf)
      (relativeFunctorVertex (sliceUnderProjection (SSet.yonedaEquiv.symm v)) a g hg)) :
    let h₀ : f ≫ sliceUnderProjection (SSet.yonedaEquiv.symm v) ≫ G = a ≫ G :=
      (Category.assoc _ _ _).symm.trans (congrArg (· ≫ G) hf)
    let h₁ : g ≫ sliceUnderProjection (SSet.yonedaEquiv.symm v) ≫ G = a ≫ G :=
      (Category.assoc _ _ _).symm.trans (congrArg (· ≫ G) hg)
    coneCounitAtApex (coneOfCosliceMap f G h₀) (coneOfCosliceMap_atApex f G h₀) =
      coneCounitAtApex (coneOfCosliceMap g G h₁) (coneOfCosliceMap_atApex g G h₁) := by
  intro h₀ h₁
  let q := sliceUnderProjection (SSet.yonedaEquiv.symm v)
  let I := relativeFunctorVertexIsoImage q a f g hf hg i
  letI : Quasicategory (sliceUnder (SSet.yonedaEquiv.symm v)) :=
    quasicategory_of_innerFibration q
  obtain ⟨Q, hz, ho, hd, hv⟩ := exists_cosliceHomotopyConePrism v I.simplicialHomotopy G
  let c := coneOfCosliceMap f G h₀
  let d := coneOfCosliceMap g G h₁
  let H : SSet.Homotopy c.val d.val := {
    h := Q
    h₀ := hz
    h₁ := ho
    rel := by
      apply SSet.hom_ext
      intro n
      apply ConcreteCategory.hom_ext
      rintro ⟨⟨x, hx⟩, t⟩
      exact False.elim hx }
  let m := Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy H)
  refine coneCounitAtApex_of_fixedApex c d m (G.app _ v)
    (coneOfCosliceMap_atApex f G h₀) (coneOfCosliceMap_atApex g G h₁) ?_ ?_
  · have h := fixedConeApexHom_arrow c d H (SSet.yonedaEquiv.symm v ≫ G) (by
      exact hv)
    rw [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply] at h
    exact h
  · apply Arrow.mk_injective
    rw [kanFunctorHomCongr_arrow]
    let V := functorHomotopyPostcomp I.simplicialHomotopy (q ≫ G)
    have hh : ((joinInr (Δ[0] : SSet.{u}) J) ▷ (Δ[1] : SSet.{u})) ≫ H.h = V.h := by
      exact hd
    have hmap : Arrow.mk
        ((hoFunctor.map ((pre (joinInr (Δ[0] : SSet.{u}) J)).app D)).toFunctor.map m) =
        Arrow.mk (Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy V)) := by
      apply Truncated.HomotopyCategory.congr_arrowMk_homMk
      change SSet.yonedaEquiv (curry H.h ≫ (pre (joinInr Δ[0] J)).app D) = SSet.yonedaEquiv (curry V.h)
      congr 1
      apply uncurry_injective
      rw [uncurry_pre_app, uncurry_curry, uncurry_curry, hh]
    refine hmap.trans ?_
    rw [functorHomotopyPostcomp_hom, functorIso_simplicialHomotopy_hom]
    have hq := mapArrow_eq_id_of_postcomp I q hf hg
      (relativeFunctorVertexIsoImage_postcomp q a f g hf hg i)
    have hG := congrArg ((hoFunctor.map ((ihom J).map G)).toFunctor.mapArrow.obj) hq
    let F := (hoFunctor.map ((ihom J).map (q ≫ G))).toFunctor
    have hF : F = (hoFunctor.map ((ihom J).map q)).toFunctor ⋙
        (hoFunctor.map ((ihom J).map G)).toFunctor := by
      unfold F
      rw [(ihom J).map_comp, hoFunctor.map_comp, Cat.Hom.comp_toFunctor]
    change F.mapArrow.obj (Arrow.mk I.hom) = _
    rw [hF]
    exact hG.trans (congrArg Arrow.mk ((hoFunctor.map ((ihom J).map G)).toFunctor.map_id
      (HomotopyCategory.mk (functorVertex a))))

end SerrePositivity.InfinityCategories.Sheaves
