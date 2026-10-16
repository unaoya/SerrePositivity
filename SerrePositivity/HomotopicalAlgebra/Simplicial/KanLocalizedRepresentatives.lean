module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.KanHomotopyClasses
public import SerrePositivity.HomotopicalAlgebra.Simplicial.KanActualHomotopy
public import Mathlib.CategoryTheory.Localization.StructuredArrow

/-! # Actual representatives for localized maps into Kan simplicial sets

Induction on a localized arrow reduces inverse anodyne steps to actual Kan
extensions. No model structure or choice of a source resolution is used.
-/

@[expose] public section
universe v uD vD
noncomputable section
open CategoryTheory CategoryTheory.Limits

namespace SerrePositivity.SimplicialModel.KanLocalizedRepresentatives
variable {D : Type uD} [Category.{vD} D] (L : SSet.{v} ⥤ D)
  [L.IsLocalization SSet.anodyneExtensions]
  {K : SSet.{v}} (hK : SSet.modelCategoryQuillen.J.rlp (terminal.from K))

include hK in
lemma map_surjective (X : SSet.{v}) :
    Function.Surjective (L.map : (X ⟶ K) → (L.obj X ⟶ L.obj K)) := by
  intro φ
  let P : CostructuredArrow L (L.obj K) → Prop :=
    fun a => ∃ f : a.left ⟶ K, L.map f = a.hom
  change P (CostructuredArrow.mk φ)
  apply Localization.induction_costructuredArrow L SSet.anodyneExtensions P
  · exact ⟨𝟙 K, L.map_id K⟩
  · intro X₁ X₂ f ψ hψ
    obtain ⟨g, hg⟩ := hψ
    exact ⟨f ≫ g, (L.map_comp f g).trans (congrArg (L.map f ≫ ·) hg)⟩
  · intro X₁ X₂ w hw ψ hψ
    obtain ⟨g, hg⟩ := hψ
    obtain ⟨f, hf⟩ := KanHomotopyExtension.exists_extension w hw hK g
    refine ⟨f, ?_⟩
    have he : L.map w ≫ L.map f = ψ :=
      (L.map_comp w f).symm.trans ((congrArg L.map hf).trans hg)
    calc
      L.map f = (Localization.isoOfHom L SSet.anodyneExtensions w hw).inv ≫
          (L.map w ≫ L.map f) := by simp
      _ = _ := congrArg
        ((Localization.isoOfHom L SSet.anodyneExtensions w hw).inv ≫ ·) he

/-- A representative of the given localized arrow, with its exact image retained. -/
def representative {X : SSet.{v}} (φ : L.obj X ⟶ L.obj K) : X ⟶ K :=
  (map_surjective L hK X φ).choose

lemma representative_map {X : SSet.{v}} (φ : L.obj X ⟶ L.obj K) :
    L.map (representative L hK φ) = φ :=
  (map_surjective L hK X φ).choose_spec

include hK in
lemma representative_isIso {X : SSet.{v}} (φ : L.obj X ⟶ L.obj K) [IsIso φ] :
    IsIso (L.map (representative L hK φ)) := by
  rw [representative_map]
  infer_instance

include hK in
lemma class_eq_of_map_eq {X : SSet.{v}} {f g : X ⟶ K} (he : L.map f = L.map g) :
    HomotopyClasses.mk f = HomotopyClasses.mk g := by
  let H := (HomotopyClasses.functor K).rightOp
  let hH := KanHomotopyClasses.rightOp_inverts K hK
  let G := Localization.lift H hH L
  let e : L ⋙ G ≅ H := Localization.fac H hH L
  have hmaps : H.map f = H.map g := by
    apply (cancel_epi (e.hom.app X)).mp
    rw [← e.hom.naturality f, ← e.hom.naturality g]
    exact congrArg (· ≫ e.hom.app K) (congrArg G.map he)
  have h := congrArg (fun p => p.unop (HomotopyClasses.mk (𝟙 K))) hmaps
  change HomotopyClasses.pre f (HomotopyClasses.mk (𝟙 K)) =
    HomotopyClasses.pre g (HomotopyClasses.mk (𝟙 K)) at h
  simpa only [HomotopyClasses.pre_mk, Category.comp_id] using h

include hK in
lemma map_eq_iff_homotopy {X : SSet.{v}} (f g : X ⟶ K) :
    L.map f = L.map g ↔ Nonempty (SSet.Homotopy f g) :=
  ⟨fun he => KanActualHomotopy.of_class_eq hK (class_eq_of_map_eq L hK he),
    fun ⟨H⟩ => AnodyneHomotopy.map_homotopy_eq L (Localization.inverts L _) H⟩

/-- Classification by actual interval homotopy, without a value model structure. -/
def homEquiv (X : SSet.{v}) :
    HomotopyClasses.obj X K ≃ (L.obj X ⟶ L.obj K) :=
  Equiv.ofBijective (HomotopyClasses.toLocalizedHom L (Localization.inverts L _) X K)
    ⟨by
      intro a b hab
      obtain ⟨f, rfl⟩ := Quot.exists_rep a
      obtain ⟨g, rfl⟩ := Quot.exists_rep b
      exact class_eq_of_map_eq L hK hab,
    fun φ => by
      obtain ⟨f, hf⟩ := map_surjective L hK X φ
      exact ⟨HomotopyClasses.mk f, hf⟩⟩

@[simp] lemma homEquiv_mk {X : SSet.{v}} (f : X ⟶ K) :
    homEquiv L hK X (HomotopyClasses.mk f) = L.map f := rfl

end SerrePositivity.SimplicialModel.KanLocalizedRepresentatives
