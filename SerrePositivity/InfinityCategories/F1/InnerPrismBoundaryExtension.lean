module

public import SerrePositivity.InfinityCategories.F1.ReplacementSquareStartCorner
public import SerrePositivity.InfinityCategories.F1.InnerAnodyneVertices
public import SerrePositivity.InfinityCategories.Core.IntervalBoundary
public import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.Inner.PushoutProduct

/-!
概要：底と二端点を固定した inner fibration に沿う prism の延長。
方針：区間の境界制限の相対内部 Hom の内ホーン充填を使う。
規約：底の prism、両端、既存の部分上の prism を全て厳密に保つ。
使われ方：比較四角形の終点側の写像の inner fibration 性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 相対内部 Hom の持ち上げにより、底と両端を固定した prism を延長する。 -/
lemma exists_prism_extension_over_fixed_endpoints_of_lifting {A B X Y : SSet.{u}}
    (q : X ⟶ Y) (i : A ⟶ B)
    (hl : HasLiftingProperty i
      (Functor.PullbackObjObj.ofHasPullback internalHom (boundary 1).ι q).π)
    (H : (Δ[1] : SSet.{u}) ⊗ A ⟶ X) (f₀ f₁ : B ⟶ X)
    (G : (Δ[1] : SSet.{u}) ⊗ B ⟶ Y)
    (hH₀ : prismEndpoint 0 A ≫ H = i ≫ f₀)
    (hH₁ : prismEndpoint 1 A ≫ H = i ≫ f₁)
    (hG : (Δ[1] ◁ i) ≫ G = H ≫ q)
    (hG₀ : prismEndpoint 0 B ≫ G = f₀ ≫ q)
    (hG₁ : prismEndpoint 1 B ≫ G = f₁ ≫ q) :
    ∃ F : (Δ[1] : SSet.{u}) ⊗ B ⟶ X,
      (Δ[1] ◁ i) ≫ F = H ∧ prismEndpoint 0 B ≫ F = f₀ ∧
      prismEndpoint 1 B ≫ F = f₁ ∧ F ≫ q = G := by
  let r := Functor.PullbackObjObj.ofHasPullback internalHom (boundary 1).ι q
  have : HasLiftingProperty i r.π := hl
  have hc : curry (intervalBoundaryDiagram f₀ f₁) ≫ (ihom (boundary 1 : SSet.{u})).map q =
      curry G ≫ (pre (boundary 1).ι).app Y := by
    apply uncurry_injective
    rw [uncurry_natural_right, uncurry_curry, uncurry_pre_app, uncurry_curry]
    rw [intervalBoundaryDiagram_restrict, hG₀, hG₁, intervalBoundaryDiagram_postcomp]
  let T := r.isPullback.lift (curry (intervalBoundaryDiagram f₀ f₁)) (curry G) hc
  have hTf : T ≫ r.fst = curry (intervalBoundaryDiagram f₀ f₁) := r.isPullback.lift_fst _ _ _
  have hTs : T ≫ r.snd = curry G := r.isPullback.lift_snd _ _ _
  have hs : CommSq (curry H) i r.π T := by
    constructor
    apply r.hom_ext
    · rw [Category.assoc, r.π_fst, Category.assoc, hTf]
      apply uncurry_injective
      change uncurry (curry H ≫ (pre (boundary 1).ι).app X) =
        uncurry (i ≫ curry (intervalBoundaryDiagram f₀ f₁))
      rw [uncurry_pre_app, uncurry_curry, uncurry_natural_left, uncurry_curry,
        intervalBoundaryDiagram_restrict, hH₀, hH₁, intervalBoundaryDiagram_naturality]
    · rw [Category.assoc, r.π_snd, Category.assoc, hTs]
      apply uncurry_injective
      change uncurry (curry H ≫ (ihom (Δ[1] : SSet.{u})).map q) = uncurry (i ≫ curry G)
      rw [uncurry_natural_right, uncurry_curry, uncurry_natural_left, uncurry_curry]
      exact hG.symm
  let F := uncurry hs.lift
  have hf : hs.lift ≫ (pre (boundary 1).ι).app X = curry (intervalBoundaryDiagram f₀ f₁) := by
    have he := congrArg (fun a : B ⟶ r.pt ↦ a ≫ r.fst) hs.fac_right
    rw [Category.assoc, r.π_fst] at he
    change hs.lift ≫ (pre (boundary 1).ι).app X = T ≫ r.fst at he
    exact he.trans hTf
  have hbd : ((boundary 1).ι ▷ B) ≫ F = intervalBoundaryDiagram f₀ f₁ := by
    have he := congrArg uncurry hf
    simpa only [uncurry_pre_app, uncurry_curry] using he
  refine ⟨F, ?_, ?_, ?_, ?_⟩
  · apply curry_injective
    rw [curry_natural_left, curry_uncurry, hs.fac_left]
  · rw [← intervalBoundaryEndpoint_ι 0 B, Category.assoc, hbd, intervalBoundaryDiagram_zero]
  · rw [← intervalBoundaryEndpoint_ι 1 B, Category.assoc, hbd, intervalBoundaryDiagram_one]
  · have he := congrArg uncurry
      (show hs.lift ≫ (ihom (Δ[1] : SSet.{u})).map q = curry G from by
        have ht := congrArg (fun a : B ⟶ r.pt ↦ a ≫ r.snd) hs.fac_right
        rw [Category.assoc, r.π_snd] at ht
        change hs.lift ≫ (ihom (Δ[1] : SSet.{u})).map q = T ≫ r.snd at ht
        exact ht.trans hTs)
    simpa only [uncurry_natural_right, uncurry_curry] using he

/-- 内 anodyne な部分上の prism は、底と両端を固定したまま延長できる。 -/
lemma exists_innerPrism_extension_over_fixed_endpoints {A B X Y : SSet.{u}}
    (q : X ⟶ Y) [InnerFibration q] (i : A ⟶ B) (hi : innerAnodyneExtensions i)
    (H : (Δ[1] : SSet.{u}) ⊗ A ⟶ X) (f₀ f₁ : B ⟶ X)
    (G : (Δ[1] : SSet.{u}) ⊗ B ⟶ Y)
    (hH₀ : prismEndpoint 0 A ≫ H = i ≫ f₀)
    (hH₁ : prismEndpoint 1 A ≫ H = i ≫ f₁)
    (hG : (Δ[1] ◁ i) ≫ G = H ≫ q)
    (hG₀ : prismEndpoint 0 B ≫ G = f₀ ≫ q)
    (hG₁ : prismEndpoint 1 B ≫ G = f₁ ≫ q) :
    ∃ F : (Δ[1] : SSet.{u}) ⊗ B ⟶ X,
      (Δ[1] ◁ i) ≫ F = H ∧ prismEndpoint 0 B ≫ F = f₀ ∧
      prismEndpoint 1 B ≫ F = f₁ ∧ F ≫ q = G := by
  let r := Functor.PullbackObjObj.ofHasPullback internalHom (boundary 1).ι q
  have : InnerFibration r.π := innerFibration_pullbackObjObjπ r
  exact exists_prism_extension_over_fixed_endpoints_of_lifting q i
    (hi _ (mem_innerFibrations r.π)) H f₀ f₁ G hH₀ hH₁ hG hG₀ hG₁

/-- 可逆 path の族を prism に戻すと、指定端点の評価を厳密に回収する。 -/
lemma equivalencePathFamilyPrism_endpoint {K X : SSet.{u}}
    (a : K ⟶ equivalencePath X) (j : Fin 2) :
    prismEndpoint j K ≫ uncurry (a ≫ equivalencePathι X) = a ≫ equivalencePathEndpoint X j := by
  rw [← curry_evaluateFunctorAt_interval, curry_uncurry]
  rfl

/-- 内 anodyne な部分の可逆 path を保つ prism の延長は、可逆 path の族へ戻る。 -/
lemma exists_equivalencePathFamily_extension {A B X : SSet.{u}}
    (i : A ⟶ B) (hi : innerAnodyneExtensions i) (a : A ⟶ equivalencePath X)
    (F : (Δ[1] : SSet.{u}) ⊗ B ⟶ X)
    (hF : (Δ[1] ◁ i) ≫ F = uncurry (a ≫ equivalencePathι X)) :
    ∃ L : B ⟶ equivalencePath X, L ≫ equivalencePathι X = curry F ∧ i ≫ L = a := by
  have hp : i ≫ curry F = a ≫ equivalencePathι X := by
    rw [← curry_natural_left, hF, curry_uncurry]
  have hv : ∀ b : B _⦋0⦌, IsEquivalencePathVertex ((curry F).app (Opposite.op ⦋0⦌) b) := by
    intro b
    obtain ⟨x, rfl⟩ := (innerAnodyne_vertex_bijective i hi).surjective b
    have hx := fullSubcomplexOnVertices_vertex (a.app (Opposite.op ⦋0⦌) x)
    have he := congrArg (fun f : A ⟶ (ihom (Δ[1] : SSet.{u})).obj X ↦
      f.app (Opposite.op ⦋0⦌) x) hp
    exact he.symm ▸ hx
  let L := fullSubcomplexLift IsEquivalencePathVertex (curry F) hv
  have hL : L ≫ equivalencePathι X = curry F := fullSubcomplexLift_ι _ _ _
  refine ⟨L, hL, ?_⟩
  have : Mono (equivalencePathι X) := by unfold equivalencePathι; infer_instance
  apply (cancel_mono (equivalencePathι X)).mp
  rw [Category.assoc, hL]
  exact hp

end SerrePositivity.InfinityCategories
