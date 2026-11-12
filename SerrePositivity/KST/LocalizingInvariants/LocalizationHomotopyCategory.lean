module

public import SerrePositivity.KST.LocalizingInvariants.LocalizationHoFactorization
public import Mathlib.CategoryTheory.Localization.Predicate

/-!
概要：quasicategory の局所化は、元の辺の類を反転する通常の h 圏の局所化でもある。
方針：通常の構成済み局所化との両比較を降下し、前合成の充満忠実性で逆同型を戻す。
規約：辺類の指定を保つ。使われ方：商の全ての実辺の元の分数表示。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants

lemma localizationHo_inverts {X Q : SSet.{u}} [Quasicategory X] [Quasicategory Q]
    (F : X ⟶ Q) (W : Set (X _⦋1⦌)) (hF : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.IsLocalization F W)
    (V : MorphismProperty (hoFunctor.obj X))
    (hV : ∀ {x y} (e : Truncated.Edge (X := (truncation 2).obj X) x y),
      V (SSet.Truncated.HomotopyCategory.homMk e) ↔ e.edge ∈ W) :
    V.IsInvertedBy (hoFunctor.map F).toFunctor := by
  intro a b f hf
  obtain ⟨x, rfl⟩ := SSet.Truncated.HomotopyCategory.mk_surjective a
  obtain ⟨y, rfl⟩ := SSet.Truncated.HomotopyCategory.mk_surjective b
  obtain ⟨e, rfl⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.homotopyCategory_homMk_surjective x y f
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (e.map ((truncation 2).map F))
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr
    (e := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex e.edge).map ((truncation 2).map F))
    (f := e.map ((truncation 2).map F)) rfl).mp (hF.choose ((hV e).mp hf))

lemma localizationHo_isLocalization_of_inverts {X Q : SSet.{u}} [Quasicategory Q]
    (F : X ⟶ Q) (W : Set (X _⦋1⦌)) (hF : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.IsLocalization F W)
    (V : MorphismProperty (hoFunctor.obj X))
    (hL : V.IsInvertedBy (hoFunctor.map F).toFunctor)
    (hV : ∀ s ∈ W, V (SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex s))) :
    (hoFunctor.map F).toFunctor.IsLocalization V := by
  let L := (hoFunctor.map F).toFunctor
  let S := Localization.Construction.lift L hL
  have hs : V.Q ⋙ S = L := Localization.Construction.fac L hL
  obtain ⟨T, ⟨e⟩⟩ := localizationHo_exists_factorization F W hF V.Q
    (fun s hs => V.Q_inverts _ (hV s hs))
  have hST : S ⋙ T ≅ 𝟭 V.Localization := by
    apply (Localization.fullyFaithfulWhiskeringLeft V.Q V V.Localization).preimageIso
    change V.Q ⋙ (S ⋙ T) ≅ V.Q ⋙ 𝟭 V.Localization
    simpa only [← Functor.assoc, hs, Functor.comp_id] using e
  have hTS : T ⋙ S ≅ 𝟭 (hoFunctor.obj Q) := by
    apply (localizationHoPre_fullyFaithful F W hF (hoFunctor.obj Q)).preimageIso
    change L ⋙ (T ⋙ S) ≅ L ⋙ 𝟭 (hoFunctor.obj Q)
    have h := Functor.isoWhiskerRight e S
    simpa only [Functor.assoc, hs, Functor.comp_id] using h
  exact ⟨hL, Functor.IsEquivalence.mk' T hST.symm hTS⟩

lemma localizationHo_isLocalization {X Q : SSet.{u}} [Quasicategory X] [Quasicategory Q]
    (F : X ⟶ Q) (W : Set (X _⦋1⦌)) (hF : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.IsLocalization F W)
    (V : MorphismProperty (hoFunctor.obj X))
    (hV : ∀ {x y} (e : Truncated.Edge (X := (truncation 2).obj X) x y),
      V (SSet.Truncated.HomotopyCategory.homMk e) ↔ e.edge ∈ W) :
    (hoFunctor.map F).toFunctor.IsLocalization V :=
  localizationHo_isLocalization_of_inverts F W hF V (localizationHo_inverts F W hF V hV)
    (fun s hs => (hV (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex s)).mpr hs)

end SerrePositivity.KST.LocalizingInvariants
