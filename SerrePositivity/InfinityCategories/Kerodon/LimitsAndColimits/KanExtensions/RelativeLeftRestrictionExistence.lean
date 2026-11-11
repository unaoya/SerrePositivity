module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RelativeLeftCanonicalExistence
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RelativeLeftKanRestrictionComparison

/-!
概要：標準局所相対余極限の存在から元の相対左 Kan 制限の頂点全射性を得る。
方針：相対標的の二成分を元と底の図式へ戻し、厳密な存在定理で同じ頂点を持ち上げる。
規約：相対 join でなく元の関手の全部分圏からの制限を扱う。
使われ方：一般の isofibration 上での相対制限の零次元境界充填。

対応節は Kerodon 7.3（Tag 02Y1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions

/-- 概要：標準局所相対余極限があれば元の相対左 Kan 制限は頂点全射。
方針：標的頂点を両立する F₀ と H₀ に分解し、元と底を等式で保つ Kan 関手を構成する。
規約：自然同型による本質的全射性ではなく、指定した標的頂点へ厳密に写す。
使われ方：元の相対制限を局所存在の下で自明 Kan にするための存在部分。 -/
lemma kanRelativeLeftKanRestriction_surjective {K C D E : SSet.{u}}
    [Quasicategory K] [Quasicategory C] [Quasicategory D] [Quasicategory E]
    (U : D ⟶ E) (hU : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.EquivalenceLifting U)
    (δ : K ⟶ C) [Mono δ] [InnerFibration δ] (hδ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful δ)
    (s : internalHom.PullbackObjObj δ U)
    (hlocal : ∀ (F₀ : K ⟶ D) (H₀ : C ⟶ E), F₀ ≫ U = δ ≫ H₀ →
      ∀ c : C _⦋0⦌, ∃ z : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanDiagram δ F₀ c),
        _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsRelativeColimitCone U z ∧ z.val ≫ U = (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanCanonicalCocone δ H₀ c).val) :
    Function.Surjective ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeLeftKanRestriction U δ s).app (Opposite.op ⦋0⦌)) := by
  intro y
  obtain ⟨F₀, hF⟩ := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv K D).surjective (s.fst.app (Opposite.op ⦋0⦌) y)
  obtain ⟨H₀, hH⟩ := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv C E).surjective (s.snd.app (Opposite.op ⦋0⦌) y)
  have hFU : F₀ ≫ U = δ ≫ H₀ := by
    have h := ConcreteCategory.congr_hom (NatTrans.congr_app s.isPullback.w (Opposite.op ⦋0⦌)) y
    change ((ihom K).map U).app (Opposite.op ⦋0⦌) (s.fst.app (Opposite.op ⦋0⦌) y) =
      ((pre δ).app E).app (Opposite.op ⦋0⦌) (s.snd.app (Opposite.op ⦋0⦌) y) at h
    rw [← hF, ← hH] at h
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex_injective h
  obtain ⟨G, hGδ, hGU, hG⟩ :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.exists_kanRelativeLeftCanonical_strict_extension_of_local_relative_colimits
      U hU δ hδ F₀ H₀ hFU (hlocal F₀ H₀ hFU)
  have hv : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.KanRelativeLeftKanVertex U δ (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex G) := by
    change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.IsRelativeLeftKanExtendedFrom U δ ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv C D).symm (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex G))
    have he : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv C D).symm (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex G) = G :=
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv C D).symm_apply_apply G
    rw [he]
    exact hG
  let x : (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeLeftKanDiagrams U δ : SSet.{u}) _⦋0⦌ := ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex G, by
    intro α
    have hα : α = 𝟙 _ := Subsingleton.elim _ _
    simpa only [hα, op_id, Functor.map_id_apply] using hv⟩
  refine ⟨x, ?_⟩
  apply Types.ext_of_isPullback
    (s.isPullback.map ((evaluation _ (Type u)).obj (Opposite.op ⦋0⦌)))
  · change (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeLeftKanRestriction U δ s ≫ s.fst).app (Opposite.op ⦋0⦌) x =
      s.fst.app (Opposite.op ⦋0⦌) y
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeLeftKanRestriction, Category.assoc, s.π_fst]
    change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (δ ≫ G) = s.fst.app (Opposite.op ⦋0⦌) y
    rw [hGδ]
    exact hF
  · change (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeLeftKanRestriction U δ s ≫ s.snd).app (Opposite.op ⦋0⦌) x =
      s.snd.app (Opposite.op ⦋0⦌) y
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeLeftKanRestriction, Category.assoc, s.π_snd]
    change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (G ≫ U) = s.snd.app (Opposite.op ⦋0⦌) y
    rw [hGU]
    exact hH

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions
