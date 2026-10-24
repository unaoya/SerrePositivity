module

public import SerrePositivity.KST.LocalizingInvariants.GeneralLocalization
public import SerrePositivity.InfinityCategories.F1B.FunctorCategories.FullSubcomplexMapping

/-!
概要：局所化の普遍性から、元の反転関手の実関手による coherent な因子化を得る。
方針：反転関手圏の頂点を取り、前合成同値の本質的全射性で持ち上げる。
規約：元の関手との実 FunctorIso を保持。使われ方：商候補から元の差の項への比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants

lemma localization_exists_factorization {X Q Y : SSet.{u}}
    [Quasicategory Q] [Quasicategory Y] (F : X ⟶ Q) (W : Set (X _⦋1⦌))
    (hF : IsLocalization F W) (H : X ⟶ Y) (hH : InvertsEdges H W) :
    ∃ K : Q ⟶ Y, Nonempty (FunctorIso (F ≫ K) H) := by
  let v : (invertingFunctors X Y W : SSet.{u}) _⦋0⦌ := ⟨functorVertex H, by
    intro a
    have ha : a = 𝟙 ⦋0⦌ := Subsingleton.elim _ _
    rw [ha, op_id, CategoryTheory.Functor.map_id_apply]
    exact hH⟩
  obtain ⟨k, ⟨e⟩⟩ := (hF.choose_spec Y).choose.isEssentiallySurjective v
  obtain ⟨K, rfl⟩ := (functorVertexEquiv Q Y).surjective k
  refine ⟨K, ⟨?_⟩⟩
  exact VertexIso.map e (invertingFunctors X Y W).ι

def localizationDescend {X Q Y : SSet.{u}} [Quasicategory Q] [Quasicategory Y]
    (F : X ⟶ Q) (W : Set (X _⦋1⦌)) (hF : IsLocalization F W)
    (H : X ⟶ Y) (hH : InvertsEdges H W) : Q ⟶ Y :=
  Classical.choose (localization_exists_factorization F W hF H hH)

def localizationDescendIso {X Q Y : SSet.{u}} [Quasicategory Q] [Quasicategory Y]
    (F : X ⟶ Q) (W : Set (X _⦋1⦌)) (hF : IsLocalization F W)
    (H : X ⟶ Y) (hH : InvertsEdges H W) :
    FunctorIso (F ≫ localizationDescend F W hF H hH) H :=
  Classical.choice (Classical.choose_spec (localization_exists_factorization F W hF H hH))

end SerrePositivity.KST.LocalizingInvariants
