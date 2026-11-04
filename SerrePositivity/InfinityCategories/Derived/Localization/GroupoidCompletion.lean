module

public import SerrePositivity.KST.LocalizingInvariants.LocalizationHomotopyCategory
public import SerrePositivity.InfinityCategories.Core.KanCharacterization

/-!
概要：任意単体集合の全ての辺を反転する実局所化は Kan 複体である。
方針：h 圏の辺生成元による帰納法で全射の可逆性を下ろし、亜群性から Kan 性を得る。
規約：始域の quasicategory 性は不要。使われ方：分母付き span の ∞ 亜群化。
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

lemma ho_inverts_all_of_inverts_all {X Q : SSet.{u}} (F : X ⟶ Q)
    (hF : InvertsEdges F Set.univ) :
    (⊤ : MorphismProperty (hoFunctor.obj X)).IsInvertedBy (hoFunctor.map F).toFunctor := by
  intro a b f _
  refine SSet.Truncated.HomotopyCategory.hom_rec (fun e => ?_) (fun f g hf hg => ?_) f
  · change IsInvertibleEdge (e.map ((truncation 2).map F))
    exact (isInvertibleEdge_congr
      (e := (edgeOfSimplex e.edge).map ((truncation 2).map F))
      (f := e.map ((truncation 2).map F)) rfl).mp (hF (Set.mem_univ _))
  · have := hf
    have := hg
    rw [CategoryTheory.Functor.map_comp]
    infer_instance

lemma localization_all_isKan {X Q : SSet.{u}} [Quasicategory Q] (F : X ⟶ Q)
    (hF : IsLocalization F Set.univ) : KanComplex Q := by
  have : (hoFunctor.map F).toFunctor.IsLocalization (⊤ : MorphismProperty (hoFunctor.obj X)) :=
    localizationHo_isLocalization_of_inverts F Set.univ hF ⊤
      (ho_inverts_all_of_inverts_all F hF.choose) (fun _ _ => trivial)
  have : IsGroupoid (hoFunctor.obj Q) := Localization.isGroupoid (hoFunctor.map F).toFunctor
  exact kanComplex_of_isGroupoid Q

def groupoidCompletion (X : SSet.{u}) : SSet.{u} := edgeLocalization X Set.univ

instance groupoidCompletion_quasicategory (X : SSet.{u}) : Quasicategory (groupoidCompletion X) :=
  edgeLocalization_quasicategory X Set.univ

def groupoidCompletionMap (X : SSet.{u}) : X ⟶ groupoidCompletion X :=
  edgeLocalizationMap X Set.univ

lemma groupoidCompletion_isLocalization (X : SSet.{u}) :
    IsLocalization (groupoidCompletionMap X) Set.univ := edgeLocalization_isLocalization X Set.univ

instance groupoidCompletion_kanComplex (X : SSet.{u}) : KanComplex (groupoidCompletion X) :=
  localization_all_isKan (groupoidCompletionMap X) (groupoidCompletion_isLocalization X)

lemma invertsAllEdges_toKan {X Y : SSet.{u}} [KanComplex Y] (F : X ⟶ Y) :
    InvertsEdges F Set.univ := by
  intro s _
  exact @IsGroupoid.all_isIso (hoFunctor.obj Y) _ (kanComplex_ho_isGroupoid Y) _ _
    (SSet.Truncated.HomotopyCategory.homMk ((edgeOfSimplex s).map ((truncation 2).map F)))

end SerrePositivity.KST.LocalizingInvariants
