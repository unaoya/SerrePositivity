module
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.LaxPullbackColimitConeExistence
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.StrongSplittingExistence

/-! # 元の lax pullback の coherent 冪等完備性
概要：両入力が冪等完備なら、同じ実 lax pullback の全 coherent 冪等図式が分裂する。
方針：両成分の強い分裂の絶対余極限を元の lax pullback の余錐として貼り合わせる。
規約：標的の完備性や lax pullback の完備性を仮定しない。使われ方：Tamme の入力。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet
open SerrePositivity.InfinityCategories


/-- 元の全 coherent 冪等図式は、同じ実 lax pullback 内に余極限を持つ。 -/
lemma perfectLaxIdempotent_hasColimit {A B C : SSet.{u}}
    [Quasicategory A] [Quasicategory B] [Quasicategory C]
    (p : A ⟶ C) (q : B ⟶ C) (hA : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentComplete A) (hB : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentComplete B)
    (r : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.CoherentIdempotent (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxPullback p q)) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasColimit r := by
  obtain ⟨sa⟩ := hA (r ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxPullbackFst p q)
  obtain ⟨sb⟩ := hB (r ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxPullbackSnd p q)
  obtain ⟨c, hc, _, _⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.exists_colimitCone_laxPullback_with_components p q r
    sa.cocone sb.cocone sa.cocone_isColimit sb.cocone_isColimit
    (sa.postcomposeCocone_isColimit p) (sb.postcomposeCocone_isColimit q)
  exact ⟨c, hc⟩

/-- 元の実 lax pullback の全 coherent 冪等図式は、元の全図式を保って強く分裂する。 -/
lemma perfectLaxPullback_isIdempotentComplete {A B C : SSet.{u}}
    [Quasicategory A] [Quasicategory B] [Quasicategory C]
    (p : A ⟶ C) (q : B ⟶ C) (hA : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentComplete A) (hB : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentComplete B) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentComplete (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxPullback p q) :=
  fun r => _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.strongSplitting_exists_of_hasColimit r (perfectLaxIdempotent_hasColimit p q hA hB r)

end SerrePositivity.KST.SConstruction
