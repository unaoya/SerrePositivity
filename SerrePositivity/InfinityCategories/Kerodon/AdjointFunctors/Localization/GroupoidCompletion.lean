module


public meta import SerrePositivity.Util.Citation

public import SerrePositivity.KST.LocalizingInvariants.LocalizationHomotopyCategory
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.GeneralLocalization
public import SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FromCategoriesToSimplicialSets.KanCharacterization

/-!
概要：任意単体集合の全ての辺を反転する実局所化は Kan 複体である。
方針：h 圏の辺生成元による帰納法で全射の可逆性を下ろし、亜群性から Kan 性を得る。
規約：始域の quasicategory 性は不要。使われ方：分母付き span の ∞ 亜群化。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants
end SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open _root_.SerrePositivity.KST.LocalizingInvariants

lemma ho_inverts_all_of_inverts_all {X Q : SSet.{u}} (F : X ⟶ Q)
    (hF : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InvertsEdges F Set.univ) :
    (⊤ : MorphismProperty (hoFunctor.obj X)).IsInvertedBy (hoFunctor.map F).toFunctor := by
  intro a b f _
  refine SSet.Truncated.HomotopyCategory.hom_rec (fun e => ?_) (fun f g hf hg => ?_) f
  · change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (e.map ((truncation 2).map F))
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr
      (e := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex e.edge).map ((truncation 2).map F))
      (f := e.map ((truncation 2).map F)) rfl).mp (hF (Set.mem_univ _))
  · have := hf
    have := hg
    rw [CategoryTheory.Functor.map_comp]
    infer_instance

lemma localization_all_isKan {X Q : SSet.{u}} [Quasicategory Q] (F : X ⟶ Q)
    (hF : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.IsLocalization F Set.univ) : KanComplex Q := by
  have : (hoFunctor.map F).toFunctor.IsLocalization (⊤ : MorphismProperty (hoFunctor.obj X)) :=
    localizationHo_isLocalization_of_inverts F Set.univ hF ⊤
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ho_inverts_all_of_inverts_all F hF.choose) (fun _ _ => trivial)
  have : IsGroupoid (hoFunctor.obj Q) := Localization.isGroupoid (hoFunctor.map F).toFunctor
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FromCategoriesToSimplicialSets.kanComplex_of_isGroupoid Q

def groupoidCompletion (X : SSet.{u}) : SSet.{u} := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.edgeLocalization X Set.univ

instance groupoidCompletion_quasicategory (X : SSet.{u}) : Quasicategory (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.groupoidCompletion X) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.edgeLocalization_quasicategory X Set.univ

def groupoidCompletionMap (X : SSet.{u}) : X ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.groupoidCompletion X :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.edgeLocalizationMap X Set.univ

lemma groupoidCompletion_isLocalization (X : SSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.IsLocalization (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.groupoidCompletionMap X) Set.univ := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.edgeLocalization_isLocalization X Set.univ

instance groupoidCompletion_kanComplex (X : SSet.{u}) : KanComplex (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.groupoidCompletion X) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.localization_all_isKan (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.groupoidCompletionMap X) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.groupoidCompletion_isLocalization X)

lemma invertsAllEdges_toKan {X Y : SSet.{u}} [KanComplex Y] (F : X ⟶ Y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InvertsEdges F Set.univ := by
  intro s _
  exact @IsGroupoid.all_isIso (hoFunctor.obj Y) _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.kanComplex_ho_isGroupoid Y) _ _
    (SSet.Truncated.HomotopyCategory.homMk ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex s).map ((truncation 2).map F)))

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section









/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HA "1.3.4.2" (partial := special) "仮定：単体集合と全辺、又は W を反転する与えられた関手（Lean が強い：任意の W で仮定なしの存在ではない）。結論：全辺の局所化、及び任意の W の小さい反転因数分解（Lean が弱い：後者は普遍性を要求しない）。"] _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.groupoidCompletion_isLocalization
