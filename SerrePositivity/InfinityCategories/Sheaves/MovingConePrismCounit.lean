module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.FunctorHomCongrArrow
public import SerrePositivity.InfinityCategories.Sheaves.MovingConePrism
public import SerrePositivity.InfinityCategories.Sheaves.RightKanMovingConeCounit
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.HomotopyRepresentative

/-!
概要：指定区間が与える頂点射は、共通図式の二つの端点の余単位を結ぶ。
方針：指定した辺と添字の座標に既存の評価則を適用する。
使われ方：離散前層の重み付き切断の自然性。
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors
open SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories
open SerrePositivity.InfinityCategories.Sheaves
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
open SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories
open SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy

namespace SerrePositivity.InfinityCategories.Sheaves

private def homotopyOfExactBoundary {A D : SSet.{u}} {F G : A ⟶ D}
    (q : A ⊗ (Δ[1] : SSet.{u}) ⟶ D) (h₀ : SSet.ι₀ ≫ q = F) (h₁ : SSet.ι₁ ≫ q = G) :
    SSet.Homotopy F G where
  h := q
  h₀ := h₀
  h₁ := h₁
  rel := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    rintro ⟨⟨x, hx⟩, i⟩
    exact False.elim hx

private lemma conePrism_diagram_morphism {J D : SSet.{u}} {p : J ⟶ D}
    (c d : JoinCone p) (H : SSet.Homotopy c.val d.val)
    (h : (joinInr (Δ[0] : SSet.{u}) J ▷ (Δ[1] : SSet.{u})) ≫ H.h =
      (functorHomotopyRefl p).h) :
    kanFunctorHomCongr c.property d.property
      ((hoFunctor.map ((pre (joinInr (Δ[0] : SSet.{u}) J)).app D)).toFunctor.map
        (Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy H))) = 𝟙 _ := by
  apply Arrow.mk_injective
  rw [kanFunctorHomCongr_arrow, ← functorHomotopyRefl_hom p]
  apply Truncated.HomotopyCategory.congr_arrowMk_homMk
  change SSet.yonedaEquiv (curry H.h ≫ (pre (joinInr Δ[0] J)).app D) =
    SSet.yonedaEquiv (curry (functorHomotopyRefl p).h)
  congr 1
  apply uncurry_injective
  rw [uncurry_pre_app, uncurry_curry, uncurry_curry, h]

private lemma conePrism_apex_morphism {J X D : SSet.{u}} {p : J ⟶ D} {v₀ v₁ : X _⦋0⦌}
    (e : X.Edge v₀ v₁) (G : X ⟶ D) (c d : JoinCone p) (H : SSet.Homotopy c.val d.val)
    (h : (joinInl (Δ[0] : SSet.{u}) J ▷ (Δ[1] : SSet.{u})) ≫ H.h =
      snd (Δ[0] : SSet.{u}) (Δ[1] : SSet.{u}) ≫ SSet.yonedaEquiv.symm e.edge ≫ G) :
    Arrow.mk (functorHomEvaluate
      (Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy H))
      (SSet.yonedaEquiv (joinInl (Δ[0] : SSet.{u}) J))) =
    Arrow.mk (Truncated.HomotopyCategory.homMk (e.map G).toTruncated) := by
  rw [functorHomEvaluate_homotopy]
  apply Truncated.HomotopyCategory.congr_arrowMk_homMk
  let z := SSet.yonedaEquiv (𝟙 (Δ[0] : SSet.{u}))
  let t : (Δ[1] : SSet.{u}) _⦋1⦌ := homotopyIntervalEdge.edge
  have ht : t = SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})) := by
    apply stdSimplex.ext
    intro i
    fin_cases i <;> rfl
  have hh := congrArg (fun f : (Δ[0] : SSet.{u}) ⊗ Δ[1] ⟶ D =>
      f.app (Opposite.op ⦋1⦌) (Basic.PinchedHom.constant z 1, t)) h
  let x := SSet.yonedaEquiv (joinInl (Δ[0] : SSet.{u}) J)
  change H.h.app _ ((Truncated.Edge.id (X := (truncation 2).obj (join Δ[0] J)) x).edge, t) =
      G.app _ e.edge
  rw [← pinchedConstant_one x]
  have hz := SSet.yonedaEquiv_comp (𝟙 (Δ[0] : SSet.{u})) (joinInl Δ[0] J)
  rw [Category.id_comp] at hz
  dsimp only [x]
  rw [hz, ← pinchedConstant_map]
  change H.h.app _ ((joinInl (Δ[0] : SSet.{u}) J).app _ (Basic.PinchedHom.constant z 1), t) =
      G.app _ e.edge
  refine hh.trans ?_
  change G.app _ ((SSet.yonedaEquiv.symm e.edge).app _ t) = _
  rw [ht, ← SSet.yonedaEquiv_comp, Category.id_comp, Equiv.apply_symm_apply]

/-- 指定区間が与える頂点射は、共通図式の二つの端点の余単位を結ぶ。
Kerodon §4.6.6（Tag 04J1）と §7.3（Tag 02Y9）。HTT 5.1.5.6 で使う指定余単位の自然性。 -/
lemma movingConePrism_counit_naturality
    {J X D : SSet.{u}} [Quasicategory D] {v₀ v₁ : X _⦋0⦌}
    (e : X.Edge v₀ v₁) (G : X ⟶ D) (w : J ⟶ sliceUnder (SSet.yonedaEquiv.symm e.edge))
    {p : J ⟶ D} (c d : JoinCone p)
    (h₀ : joinMap (stdSimplex.δ (1 : Fin 2)) (𝟙 J) ≫ sliceUnderUncurry w ≫ G = c.val)
    (h₁ : joinMap (stdSimplex.δ (0 : Fin 2)) (𝟙 J) ≫ sliceUnderUncurry w ≫ G = d.val)
    (hp : (w ≫ sliceUnderProjection (SSet.yonedaEquiv.symm e.edge)) ≫ G = p) :
    ∃ a : (HomotopyCategory.mk c.vertex : hoFunctor.obj D) ⟶ HomotopyCategory.mk d.vertex,
      Arrow.mk a = Arrow.mk (Truncated.HomotopyCategory.homMk (e.map G).toTruncated) ∧
      constantFunctorHomMap J a ≫ coneCounitHom d = coneCounitHom c := by
  let Q := movingConePrism w ≫ G
  obtain ⟨hz, ho, hd, hv⟩ := movingConePrism_boundaries w
  let H : SSet.Homotopy c.val d.val := homotopyOfExactBoundary Q
    (by dsimp only [Q]; rw [← Category.assoc, hz, Category.assoc, h₀])
    (by dsimp only [Q]; rw [← Category.assoc, ho, Category.assoc, h₁])
  let m := Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy H)
  let a := functorHomEvaluate m (SSet.yonedaEquiv (joinInl (Δ[0] : SSet.{u}) J))
  refine ⟨a, ?_, ?_⟩
  · exact conePrism_apex_morphism e G c d H (by
      dsimp only [H, homotopyOfExactBoundary, Q]
      rw [← Category.assoc, hv, Category.assoc])
  · have hj := conePrism_diagram_morphism c d H (by
      dsimp only [H, homotopyOfExactBoundary, Q, functorHomotopyRefl]
      rw [← Category.assoc, hd, Category.assoc, hp])
    have h := coneCounitHom_morphism_naturality c d m
    exact h.trans (by rw [hj, Category.comp_id])

end SerrePositivity.InfinityCategories.Sheaves
