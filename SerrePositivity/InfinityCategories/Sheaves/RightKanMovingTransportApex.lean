module

public import SerrePositivity.InfinityCategories.Sheaves.RightKanCounitAtApex
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.RightKanLimitComposition
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.FunctorHomCongrArrow
public import SerrePositivity.InfinityCategories.Sheaves.RightKanMovingCanonicalCounit
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RightKanCanonicalShapeLaws

/-!
概要：同じ指定余単位による輸送を共通添字へ制限し、その極限錐の比較射の頂点を元の辺として回収する。
方針：指定した辺と添字の座標に既存の評価則を適用する。
使われ方：離散前層の重み付き切断の自然性。
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Sheaves
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
open SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories
open SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy
open CategoryTheory MonoidalCategory MonoidalClosed Limits SSet

namespace SerrePositivity.InfinityCategories.Sheaves

private lemma comp_arrow {T : Type u} [Category.{u} T] {a b c x y z : T}
    (f : a ⟶ b) (g : b ⟶ c) (F : x ⟶ y) (G : y ⟶ z)
    (hf : Arrow.mk f = Arrow.mk F) (hg : Arrow.mk g = Arrow.mk G) :
    Arrow.mk (f ≫ g) = Arrow.mk (F ≫ G) := by
  obtain ⟨ha, hb, hf⟩ := (Arrow.mk_eq_mk_iff _ _).1 hf
  obtain ⟨_, hc, hg⟩ := (Arrow.mk_eq_mk_iff _ _).1 hg
  subst a b c
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at hf hg
  rw [hf, hg]

private lemma restrictedRightKanCounit_atApex
    {J K C D : SSet.{u}} [Quasicategory D]
    {δ : K ⟶ C} {O : K ⟶ D} {G : C ⟶ D}
    {α : SSet.Homotopy (δ ≫ G) O} {v : C _⦋0⦌}
    (t : RightKanConeTransport δ O G α v) (j : J ⟶ rightKanShape δ v) :
    let c := rightKanCanonicalCone δ G v
    let rc := restrictJoinCone c j
    let rt := restrictJoinCone t.cone j
    let hrc := (restrictJoinCone_vertex c j).trans (rightKanCanonicalCone_vertex δ G v)
    let hrt := (restrictJoinCone_vertex t.cone j).trans t.cone_vertex
    let a := Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy α)
    coneCounitAtApex rt hrt = coneCounitAtApex rc hrc ≫
      (hoFunctor.map ((pre j).app D)).toFunctor.map
        ((hoFunctor.map ((pre (rightKanProjection δ v)).app D)).toFunctor.map a) := by
  intro c rc rt hrc hrt a
  let M := (hoFunctor.map ((pre j).app D)).toFunctor
  let B := (hoFunctor.map ((pre (rightKanProjection δ v)).app D)).toFunctor.map a
  let c' := coneCounitAtApex c (rightKanCanonicalCone_vertex δ G v)
  have ht := congrArg Arrow.mk (coneCounitAtApex_shapeRestriction t.cone j t.cone_vertex)
  have hc := congrArg Arrow.mk
    (coneCounitAtApex_shapeRestriction c j (rightKanCanonicalCone_vertex δ G v))
  rw [kanFunctorHomCongr_arrow] at ht hc
  apply Arrow.mk_injective
  calc
    _ = M.mapArrow.obj (Arrow.mk (coneCounitAtApex t.cone t.cone_vertex)) := ht.symm
    _ = M.mapArrow.obj (Arrow.mk (c' ≫ B)) :=
      congrArg (fun m => M.mapArrow.obj (Arrow.mk m)) (rightKan_transport_counit_atApex t)
    _ = Arrow.mk (M.map c' ≫ M.map B) :=
      congrArg Arrow.mk (M.map_comp c' B)
    _ = _ := comp_arrow _ _ _ _ hc rfl

private lemma restrictedRightKanDiagramArrow
    {J K C D : SSet.{u}} {δ : K ⟶ C} {O : K ⟶ D} {G : C ⟶ D}
    (α : SSet.Homotopy (δ ≫ G) O) {v : C _⦋0⦌} (j : J ⟶ rightKanShape δ v) :
    let r := rightKanProjection δ v
    let a := Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy α)
    Arrow.mk ((hoFunctor.map ((pre j).app D)).toFunctor.map
      ((hoFunctor.map ((pre r).app D)).toFunctor.map a)) =
      Arrow.mk (Truncated.HomotopyCategory.homMk
        (functorEdgeOfSimplicialHomotopy (functorHomotopyPrecomp α (j ≫ r)))) := by
  intro r a
  dsimp only [a]
  rw [← functorHomotopyPrecomp_hom, ← functorHomotopyPrecomp_hom]
  apply functorHomotopy_hom_arrow_of_h_eq
  dsimp only [functorHomotopyPrecomp]
  rw [← Category.assoc, ← comp_whiskerRight]

private lemma cone_apex_eq_of_counitAtApex_fac
    {J D : SSet.{u}} [Quasicategory D] {p : J ⟶ D} {c d : JoinCone p}
    {x y : D _⦋0⦌} (hc : c.vertex = x) (hd : d.vertex = y)
    (hl : IsLimitCone d) (k : (HomotopyCategory.mk c : hoFunctor.obj (sliceOver p)) ⟶ HomotopyCategory.mk d)
    (a : (HomotopyCategory.mk x : hoFunctor.obj D) ⟶ HomotopyCategory.mk y)
    (h : constantFunctorHomMap J a ≫ coneCounitAtApex d hd = coneCounitAtApex c hc) :
    a = eqToHom (congrArg HomotopyCategory.mk hc).symm ≫
      (hoFunctor.map (sliceOverProjection p)).toFunctor.map k ≫ eqToHom (congrArg HomotopyCategory.mk hd) := by
  subst x y
  simp only [coneCounitAtApex, eqToHom_refl, constantFunctorHomMap_id, Category.id_comp] at h
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  exact cone_apex_eq_of_counit_fac hl k a h

private lemma restrictedCosliceRightKanCounit
    {J K C D : SSet.{u}} [Quasicategory D] {δ : K ⟶ C} {O : K ⟶ D} {G : C ⟶ D}
    {α : SSet.Homotopy (δ ≫ G) O} {v : C _⦋0⦌}
    (t : RightKanConeTransport δ O G α v) (j : J ⟶ rightKanShape δ v)
    (s : J ⟶ K) (hs : j ≫ rightKanProjection δ v = s)
    (H : j ≫ rightKanDiagram δ O v = s ≫ O) :
    let q := sliceUnderProjection (SSet.yonedaEquiv.symm v)
    let f := j ≫ pullback.fst q δ
    let c := (restrictJoinCone t.cone j).cast H
    let hc := (JoinCone.vertex_cast _ H).trans ((restrictJoinCone_vertex t.cone j).trans t.cone_vertex)
    ∀ (hf : f ≫ q ≫ G = (s ≫ δ) ≫ G),
    let d := coneOfCosliceMap f G hf
    let b := Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy (functorHomotopyPrecomp α s))
    coneCounitAtApex c hc = coneCounitAtApex d (coneOfCosliceMap_atApex f G hf) ≫
      kanFunctorHomCongr (Category.assoc s δ G).symm rfl b := by
  intro q f c hc hf d b
  let r := rightKanProjection δ v
  let c₀ := rightKanCanonicalCone δ G v
  let rc := restrictJoinCone c₀ j
  let rt := restrictJoinCone t.cone j
  let hrc := (restrictJoinCone_vertex c₀ j).trans (rightKanCanonicalCone_vertex δ G v)
  let hrt := (restrictJoinCone_vertex t.cone j).trans t.cone_vertex
  have hD : j ≫ rightKanDiagram δ (δ ≫ G) v = (s ≫ δ) ≫ G := by
    rw [rightKanDiagram, ← Category.assoc, hs, Category.assoc]
  have hv : rc.cast hD = d := by
    apply Subtype.ext
    change joinMap (𝟙 Δ[0]) j ≫ (rightKanCanonicalShape δ v ≫ G) = sliceUnderUncurry f ≫ G
    rw [sliceUnderUncurry_precomp, Category.assoc]
    rfl
  have hL : Arrow.mk (coneCounitAtApex c hc) = Arrow.mk (coneCounitAtApex rt hrt) :=
    (congrArg Arrow.mk (coneCounitAtApex_cast rt H hrt)).trans (kanFunctorHomCongr_arrow _ _ _)
  have hR : Arrow.mk (coneCounitAtApex rc hrc) =
      Arrow.mk (coneCounitAtApex d (coneOfCosliceMap_atApex f G hf)) := by
    have h := (congrArg Arrow.mk (coneCounitAtApex_cast rc hD hrc)).trans
      (kanFunctorHomCongr_arrow _ _ _)
    rw [← h]
    have hi : ∀ (z : JoinCone ((s ≫ δ) ≫ G)) (hz : z = d) (ap : z.vertex = G.app _ v),
        coneCounitAtApex z ap = coneCounitAtApex d (coneOfCosliceMap_atApex f G hf) := by
      intro z hz ap
      subst z
      rfl
    exact congrArg Arrow.mk (hi _ hv _)
  let a := Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy α)
  let B := (hoFunctor.map ((pre j).app D)).toFunctor.map
    ((hoFunctor.map ((pre r).app D)).toFunctor.map a)
  have hb : Arrow.mk B = Arrow.mk (kanFunctorHomCongr (Category.assoc s δ G).symm rfl b) := by
    have h := restrictedRightKanDiagramArrow α j
    dsimp only at h
    rw [hs] at h
    exact h.trans (kanFunctorHomCongr_arrow _ _ _).symm
  apply Arrow.mk_injective
  exact hL.trans ((congrArg Arrow.mk (restrictedRightKanCounit_atApex t j)).trans
    (comp_arrow _ _ _ _ hR hb))

/-- 同じ指定余単位による輸送を共通添字へ制限し、その極限錐の比較射の頂点を元の辺として回収する。
Kerodon Definition 7.3.1.2（Tag 02Y9）と HTT 5.1.5.6 の指定局所比較。 -/
lemma rightKanMovingIndex_transportApex
    {J K C D : SSet.{u}} [Quasicategory C] [Quasicategory D]
    {δ : K ⟶ C} {O : K ⟶ D} {G : C ⟶ D} (α : SSet.Homotopy (δ ≫ G) O)
    {v₀ v₁ : C _⦋0⦌} (e : C.Edge v₀ v₁)
    (j₀ : J ⟶ rightKanShape δ v₀) (j₁ : J ⟶ rightKanShape δ v₁)
    (hj : j₀ ≫ rightKanProjection δ v₀ = j₁ ≫ rightKanProjection δ v₁)
    (hface : rightKanMovingIndexFace δ (SSet.yonedaEquiv.symm e.edge)
      e.δ_one_yonedaEquiv_symm e.δ_zero_yonedaEquiv_symm j₀ j₁)
    (t₀ : RightKanConeTransport δ O G α v₀) (t₁ : RightKanConeTransport δ O G α v₁) :
    let s := j₀ ≫ rightKanProjection δ v₀
    ∀ (h₀ : j₀ ≫ rightKanDiagram δ O v₀ = s ≫ O)
      (h₁ : j₁ ≫ rightKanDiagram δ O v₁ = s ≫ O),
    let c := (restrictJoinCone t₀.cone j₀).cast h₀
    let d := (restrictJoinCone t₁.cone j₁).cast h₁
    let hc := (JoinCone.vertex_cast _ h₀).trans ((restrictJoinCone_vertex t₀.cone j₀).trans t₀.cone_vertex)
    let hd := (JoinCone.vertex_cast _ h₁).trans ((restrictJoinCone_vertex t₁.cone j₁).trans t₁.cone_vertex)
    ∀ (hl : IsLimitCone d)
      (k : (HomotopyCategory.mk c : hoFunctor.obj (sliceOver (s ≫ O))) ⟶ HomotopyCategory.mk d),
    Truncated.HomotopyCategory.homMk (e.map G).toTruncated =
      eqToHom (congrArg HomotopyCategory.mk hc).symm ≫
        (hoFunctor.map (sliceOverProjection (s ≫ O))).toFunctor.map k ≫
          eqToHom (congrArg HomotopyCategory.mk hd) := by
  intro s h₀ h₁ c d hc hd hl k
  let q₀ := sliceUnderProjection (SSet.yonedaEquiv.symm v₀)
  let q₁ := sliceUnderProjection (SSet.yonedaEquiv.symm v₁)
  let a₀ := j₀ ≫ pullback.fst q₀ δ
  let a₁ := j₁ ≫ pullback.fst q₁ δ
  have hA {v : C _⦋0⦌} (j : J ⟶ rightKanShape δ v) (hs : j ≫ rightKanProjection δ v = s) :
      (j ≫ pullback.fst (sliceUnderProjection (SSet.yonedaEquiv.symm v)) δ) ≫
          sliceUnderProjection (SSet.yonedaEquiv.symm v) ≫ G = (s ≫ δ) ≫ G := by
    simp only [Category.assoc]
    rw [← Category.assoc (pullback.fst _ _) _ G, pullback.condition]
    simp only [← Category.assoc]
    exact congrArg (fun f => (f ≫ δ) ≫ G) hs
  let hf₀ := hA j₀ rfl
  let hf₁ := hA j₁ hj.symm
  have h₀a := restrictedCosliceRightKanCounit t₀ j₀ s rfl h₀ hf₀
  have h₁a := restrictedCosliceRightKanCounit t₁ j₁ s hj.symm h₁ hf₁
  have hmove := rightKanMovingIndex_cosliceCounit δ G e j₀ j₁ hface hf₀ hf₁
  apply cone_apex_eq_of_counitAtApex_fac hc hd hl k
  rw [h₁a, ← Category.assoc, hmove, ← h₀a]

end SerrePositivity.InfinityCategories.Sheaves
