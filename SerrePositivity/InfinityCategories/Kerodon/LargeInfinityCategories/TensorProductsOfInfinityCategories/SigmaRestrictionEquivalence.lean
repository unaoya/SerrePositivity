module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.SigmaLeftKanSiftedPreservation
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.SigmaRestrictionFullyFaithful
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.FullyFaithfulEquivalence

/-!
概要：元の P_Σ Yoneda 制限は、小さい sifted 余極限を保つ全関手 ∞ 圏の同値である。
方針：元の左 Kan 延長の保存性と指定単位の回収を用いて本質的全射性を構成する。
規約：元の制限射を順射に持ち、全自然変換と高次単体を保持する。
使われ方：P_Σ の自由 sifted 余極限完備化としての普遍性。

対応節は Kerodon 9.7（Tag 06ZD）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories

/-- 概要：元の sifted 保存関手を、同じ保存関手全部分 ∞ 圏の頂点として束ねる。
方針：全関手の元の頂点に、全小 sifted 余極限の保存証拠を添える。
規約：元の関手の全単体を変更しない。
使われ方：Yoneda 制限の本質的全射性の実際の前像。 -/
def siftedContinuousFunctorVertex {X D : SSet.{u + 1}} (G : X ⟶ D)
    (hG : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.PreservesSmallSiftedColimits G) : (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.SiftedContinuousFunctorInfinity X D) _⦋0⦌ :=
  ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex G, by
    intro a
    have ha : a = 𝟙 _ := Subsingleton.elim _ _
    subst a
    have hrec : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv X D).symm (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex G) = G :=
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv X D).symm_apply_apply G
    simpa only [op_id, CategoryTheory.Functor.map_id_apply, hrec] using hG⟩

variable (C : SSet.{u}) [Quasicategory C]
  (hC : ∀ (J : Type u) [Finite J] (d : nerve (Discrete J) ⟶ C.op), _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasLimit d)
  (D : SSet.{u + 1}) [Quasicategory D] (hD : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.HasSmallSiftedColimits D)
include hC hD

/-- 概要：元の Yoneda 制限は、sifted 余極限を持つ標的に対して本質的全射である。
方針：元の図式を左 Kan 延長し、証明した保存性と指定単位の回収同型を使う。
規約：保存関手の存在を追加で仮定しない。
使われ方：元の制限射の全 ∞ 圏同値の構成。 -/
lemma sigmaSiftedContinuousRestriction_isEssentiallySurjective :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsEssentiallySurjective (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.sigmaSiftedContinuousRestriction C D) := by
  intro v
  let F₀ := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv ((SSet.uliftFunctor.{u + 1, u}).obj C) D).symm v
  obtain ⟨G, β, hβ⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sigma_exists_leftKanExtension hC hD F₀
  have hG := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sigmaLeftKanExtension_preservesSmallSiftedColimits β hβ
  refine ⟨siftedContinuousFunctorVertex G hG, ?_⟩
  have hv : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F₀ = v := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv _ _).apply_symm_apply v
  change Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sigmaYonedaInfinityMap C ≫ G)) v)
  rw [← hv]
  exact ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sigmaLeftKanExtensionRecoveryIso β hβ⟩

/-- 概要：元の P_Σ Yoneda 制限射自身は全 ∞ 圏同値である。
方針：同じ制限射の全写像空間での充満忠実性と本質的全射性を合わせる。
規約：小さい底の有限余積と標的の sifted 余極限の存在を明示する。
使われ方：P_Σ の自由 sifted 余極限完備化の普遍性。 -/
lemma sigmaSiftedContinuousRestriction_isQCatEquivalence :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.sigmaSiftedContinuousRestriction C D) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.isQCatEquivalence_of_isFullyFaithful_of_isEssentiallySurjective _
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sigmaSiftedContinuousRestriction_isFullyFaithful C hC D)
    (sigmaSiftedContinuousRestriction_isEssentiallySurjective C hC D hD)

/-- 概要：同じ元の制限を順射に持つ、保存関手 ∞ 圏と元の関手 ∞ 圏の全同値。
方針：元の制限の証明済みの同値性から逆関手と両合成同型を回収する。
規約：元の全自然変換と高次単体を含む関手空間の同値で述べる。
使われ方：任意の C 上の図式の、sifted 保存延長の普遍的選択。 -/
def sigmaSiftedContinuousRestrictionEquivalence :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.SiftedContinuousFunctorInfinity (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.SigmaPresheafInfinity C) D)
      ((ihom ((SSet.uliftFunctor.{u + 1, u}).obj C)).obj D) :=
  (sigmaSiftedContinuousRestriction_isQCatEquivalence C hC D hD).choose

/-- 概要：構成した普遍性同値の順射は、元の Yoneda 制限そのものである。
方針：同値データの順射の定義を展開する。
規約：同値な別の制限写像で代用しない。
使われ方：元の Yoneda の単位・余単位と他の構成の照合。 -/
lemma sigmaSiftedContinuousRestrictionEquivalence_hom :
    (sigmaSiftedContinuousRestrictionEquivalence C hC D hD).hom =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.sigmaSiftedContinuousRestriction C D := rfl

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories
