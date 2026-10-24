module

public import SerrePositivity.InfinityCategories.F1B.KanExtension.RelativeLeftCanonicalExistence
public import SerrePositivity.InfinityCategories.F1B.KanExtension.RelativeLeftKanRestrictionComparison

/-!
概要：標準局所相対余極限の存在から元の相対左 Kan 制限の頂点全射性を得る。
方針：相対標的の二成分を元と底の図式へ戻し、厳密な存在定理で同じ頂点を持ち上げる。
規約：相対 join でなく元の関手の全部分圏からの制限を扱う。
使われ方：一般の isofibration 上での相対制限の零次元境界充填。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F1B

/-- 概要：標準局所相対余極限があれば元の相対左 Kan 制限は頂点全射。
方針：標的頂点を両立する F₀ と H₀ に分解し、元と底を等式で保つ Kan 関手を構成する。
規約：自然同型による本質的全射性ではなく、指定した標的頂点へ厳密に写す。
使われ方：元の相対制限を局所存在の下で自明 Kan にするための存在部分。 -/
lemma kanRelativeLeftKanRestriction_surjective {K C D E : SSet.{u}}
    [Quasicategory K] [Quasicategory C] [Quasicategory D] [Quasicategory E]
    (U : D ⟶ E) (hU : SerrePositivity.InfinityCategories.F1B.EquivalenceLifting U)
    (δ : K ⟶ C) [Mono δ] [InnerFibration δ] (hδ : IsFullyFaithful δ)
    (s : internalHom.PullbackObjObj δ U)
    (hlocal : ∀ (F₀ : K ⟶ D) (H₀ : C ⟶ E), F₀ ≫ U = δ ≫ H₀ →
      ∀ c : C _⦋0⦌, ∃ z : JoinCocone (leftKanDiagram δ F₀ c),
        IsRelativeColimitCone U z ∧ z.val ≫ U = (leftKanCanonicalCocone δ H₀ c).val) :
    Function.Surjective ((kanRelativeLeftKanRestriction U δ s).app (Opposite.op ⦋0⦌)) := by
  intro y
  obtain ⟨F₀, hF⟩ := (functorVertexEquiv K D).surjective (s.fst.app (Opposite.op ⦋0⦌) y)
  obtain ⟨H₀, hH⟩ := (functorVertexEquiv C E).surjective (s.snd.app (Opposite.op ⦋0⦌) y)
  have hFU : F₀ ≫ U = δ ≫ H₀ := by
    have h := ConcreteCategory.congr_hom (NatTrans.congr_app s.isPullback.w (Opposite.op ⦋0⦌)) y
    change ((ihom K).map U).app (Opposite.op ⦋0⦌) (s.fst.app (Opposite.op ⦋0⦌) y) =
      ((pre δ).app E).app (Opposite.op ⦋0⦌) (s.snd.app (Opposite.op ⦋0⦌) y) at h
    rw [← hF, ← hH] at h
    exact functorVertex_injective h
  obtain ⟨G, hGδ, hGU, hG⟩ :=
    exists_kanRelativeLeftCanonical_strict_extension_of_local_relative_colimits
      U hU δ hδ F₀ H₀ hFU (hlocal F₀ H₀ hFU)
  have hv : KanRelativeLeftKanVertex U δ (functorVertex G) := by
    change IsRelativeLeftKanExtendedFrom U δ ((functorVertexEquiv C D).symm (functorVertex G))
    have he : (functorVertexEquiv C D).symm (functorVertex G) = G :=
      (functorVertexEquiv C D).symm_apply_apply G
    rw [he]
    exact hG
  let x : (kanRelativeLeftKanDiagrams U δ : SSet.{u}) _⦋0⦌ := ⟨functorVertex G, by
    intro α
    have hα : α = 𝟙 _ := Subsingleton.elim _ _
    simpa only [hα, op_id, Functor.map_id_apply] using hv⟩
  refine ⟨x, ?_⟩
  apply Types.ext_of_isPullback
    (s.isPullback.map ((evaluation _ (Type u)).obj (Opposite.op ⦋0⦌)))
  · change (kanRelativeLeftKanRestriction U δ s ≫ s.fst).app (Opposite.op ⦋0⦌) x =
      s.fst.app (Opposite.op ⦋0⦌) y
    rw [kanRelativeLeftKanRestriction, Category.assoc, s.π_fst]
    change functorVertex (δ ≫ G) = s.fst.app (Opposite.op ⦋0⦌) y
    rw [hGδ]
    exact hF
  · change (kanRelativeLeftKanRestriction U δ s ≫ s.snd).app (Opposite.op ⦋0⦌) x =
      s.snd.app (Opposite.op ⦋0⦌) y
    rw [kanRelativeLeftKanRestriction, Category.assoc, s.π_snd]
    change functorVertex (G ≫ U) = s.snd.app (Opposite.op ⦋0⦌) y
    rw [hGU]
    exact hH

end SerrePositivity.InfinityCategories.F1B
