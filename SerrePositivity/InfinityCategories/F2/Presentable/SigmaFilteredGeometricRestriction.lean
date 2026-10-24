module

public import SerrePositivity.InfinityCategories.F2.Presentable.SigmaFilteredGeometricLeftKan
public import SerrePositivity.InfinityCategories.F2.Presentable.SigmaRestrictionEquivalence

/-!
概要：filtered 余極限と幾何学的実現だけを持つ標的への sifted 保存延長の普遍性。
方針：構成した左 Kan 延長の保存性と元の制限の充満忠実性を組み合わせる。
規約：標的に全小 sifted 余極限を追加入力しない。
使われ方：弱い標的条件での P_Σ Yoneda 制限の全同値。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable
open HomotopyLimits Ind
variable (C : SSet.{u}) [Quasicategory C]
  (hC : ∀ (J : Type u) [Finite J] (d : nerve (Discrete J) ⟶ C.op), HasLimit d)
  (D : SSet.{u + 1}) [Quasicategory D]
  (hD : HasSmallKappaFilteredColimits Cardinal.aleph0 D)
  (hG : HasSmallGeometricRealizations D)
include hC hD hG

/-- 概要：元の Yoneda 制限は、filtered 余極限と実現を持つ標的に対して本質的全射。
方針：元の図式を左 Kan 延長し、証明した保存性と指定単位の回収同型を使う。
規約：保存関手の存在を追加で仮定しない。
使われ方：元の制限射の全 ∞ 圏同値の構成。 -/
lemma sigmaSiftedContinuousRestriction_isEssentiallySurjective_of_filtered_geometric :
    IsEssentiallySurjective (sigmaSiftedContinuousRestriction C D) := by
  intro v
  let F₀ := (functorVertexEquiv ((SSet.uliftFunctor.{u + 1, u}).obj C) D).symm v
  obtain ⟨G, β, hβ⟩ := sigma_exists_leftKanExtension_of_filtered_geometric hC hD hG F₀
  have hG := sigmaLeftKanExtension_preservesSmallSiftedColimits β hβ
  refine ⟨siftedContinuousFunctorVertex G hG, ?_⟩
  have hv : functorVertex F₀ = v := (functorVertexEquiv _ _).apply_symm_apply v
  change Nonempty (VertexIso (functorVertex (sigmaYonedaInfinityMap C ≫ G)) v)
  rw [← hv]
  exact ⟨sigmaLeftKanExtensionRecoveryIso β hβ⟩

/-- 概要：元の P_Σ Yoneda 制限射自身は全 ∞ 圏同値である。
方針：同じ制限射の全写像空間での充満忠実性と本質的全射性を合わせる。
規約：標的には filtered 余極限と幾何学的実現のみを要求する。
使われ方：P_Σ の自由 sifted 余極限完備化の普遍性。 -/
lemma sigmaSiftedContinuousRestriction_isQCatEquivalence_of_filtered_geometric :
    IsQCatEquivalence (sigmaSiftedContinuousRestriction C D) :=
  isQCatEquivalence_of_isFullyFaithful_of_isEssentiallySurjective _
    (sigmaSiftedContinuousRestriction_isFullyFaithful C hC D)
    (sigmaSiftedContinuousRestriction_isEssentiallySurjective_of_filtered_geometric C hC D hD hG)

/-- 概要：同じ元の制限を順射に持つ、保存関手 ∞ 圏と元の関手 ∞ 圏の全同値。
方針：元の制限の証明済みの同値性から逆関手と両合成同型を回収する。
規約：元の全自然変換と高次単体を含む関手空間の同値で述べる。
使われ方：任意の C 上の図式の、sifted 保存延長の普遍的選択。 -/
def sigmaSiftedContinuousRestrictionEquivalenceOfFilteredGeometric :
    QCatEquivalence (SiftedContinuousFunctorInfinity (SigmaPresheafInfinity C) D)
      ((ihom ((SSet.uliftFunctor.{u + 1, u}).obj C)).obj D) :=
  (sigmaSiftedContinuousRestriction_isQCatEquivalence_of_filtered_geometric C hC D hD hG).choose

/-- 概要：構成した普遍性同値の順射は、元の Yoneda 制限そのものである。
方針：同値データの順射の定義を展開する。
規約：同値な別の制限写像で代用しない。
使われ方：元の Yoneda の単位・余単位と他の構成の照合。 -/
lemma sigmaSiftedContinuousRestrictionEquivalenceOfFilteredGeometric_hom :
    (sigmaSiftedContinuousRestrictionEquivalenceOfFilteredGeometric C hC D hD hG).hom =
      sigmaSiftedContinuousRestriction C D := rfl

end SerrePositivity.InfinityCategories.F2.Presentable
