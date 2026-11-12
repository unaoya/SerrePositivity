module
public import SerrePositivity.KST.SConstruction.Cofinality.RelativeFlagImageComponents

/-!
概要：相対旗の像成分の全図式を元の同じ全多次数の始域へ戻す。
方針：連結パラメータ内で本質像所属を輸送し、充満忠実性で全関手を回収する。
規約：点ごとの射だけを独立に選ばず、一つの全関手同型を得る。
使われ方：相対 S• の零成分と元の始域の図式の比較。
-/

@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction.Cofinality
open CategoryTheory MonoidalClosed SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 概要：始域の全旗から相対旗への元の射は充満忠実。
方針：相対旗の全包含で反映し、元の完全射の後合成の充満忠実性を使う。
規約：相対旗全体への本質全射性は主張しない。
使われ方：像成分の全図式を元の始域へ回収する際の比較の一意性。 -/
lemma completionSourceToRelativeFlags_isFullyFaithful (r : ℕ)
    (ι : Fin r → SimplexCategoryᵒᵖ) {X Y : StableModel.{u}} (f : X ⟶ Y)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val) (K : SSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful (multiSourceToRelativeFlags stableWideCofinalitySupply r ι f hf K) := by
  apply (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.isFullyFaithful_fullSubcomplexOnVertices_ι _ _).cancel_right
  exact (multiSourceToRelativeFlags_inclusion stableWideCofinalitySupply r ι f hf K).symm ▸
    (multiSEndofunctor_map_isFullyFaithful r ι f hf.2.1).postcompose K

/-- 概要：連結な相対旗の一頂点が元の像に入れば全旗が元の始域から回収できる。
方針：wide の成分内で全頂点の像所属を輸送し、全図式回収を適用する。
規約：回収は指定された同じ多次数の射を通る一つの全関手同型。
使われ方：相対 S• の像成分における元の始域の同定。 -/
theorem exists_multiSourceFamily_of_relative_component (r : ℕ)
    (ι : Fin r → SimplexCategoryᵒᵖ) {X Y : StableModel.{u}} (f : X ⟶ Y)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val)
    {K : SSet.{u}} [K.IsPreconnected]
    (F : K ⟶ (LocalizingInvariants.completionCofiberWide
      (((multiSEndofunctor r).obj ι).map f).val : SSet.{u}))
    (k₀ : K _⦋0⦌)
    (hk₀ : (F.app (Opposite.op ⦋0⦌) k₀).val ∈
      LocalizingInvariants.completionEssentialImage (((multiSEndofunctor r).obj ι).map f).val) :
    ∃ G : K ⟶ (((multiSEndofunctor r).obj ι).obj X).carrier,
      Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (G ≫ (((multiSEndofunctor r).obj ι).map f).val)
        (F ≫ (LocalizingInvariants.completionCofiberWide
          (((multiSEndofunctor r).obj ι).map f).val).ι)) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.exists_diagram_in_fullyFaithful_source _
    (multiSEndofunctor_map_isFullyFaithful r ι f hf.2.1)
  intro k
  have hh : SSet.π₀.mk (F.app (Opposite.op ⦋0⦌) k₀) =
      SSet.π₀.mk (F.app (Opposite.op ⦋0⦌) k) :=
    congrArg (SSet.mapπ₀ F) (Subsingleton.elim (SSet.π₀.mk k₀) (SSet.π₀.mk k))
  exact (completionMultiWideComponent_image_iff r ι f hf _ _ hh).mp hk₀

end SerrePositivity.KST.SConstruction.Cofinality
