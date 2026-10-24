module

public import SerrePositivity.InfinityCategories.F1B.KanExtension.RelativeJoinRelativeUniversalRestriction
public import SerrePositivity.InfinityCategories.Core.FullyFaithfulBoundary

/-!
概要：局所相対余極限の存在から相対普遍図式の制限の自明 Kan 性を得る。
方針：厳密な大域図式の組み立てで頂点を持ち上げ、充満忠実性と inner 性を合わせる。
規約：標的の整合する図式の各組に対して局所相対余極限を要求する。
使われ方：相対 Kan 図式の coherent な選択と可縮な一意性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F1B

/-- 概要：局所相対余極限が存在すれば相対普遍図式の制限は頂点で全射。
方針：標的の頂点を整合する二つの図式に分解し、厳密な大域図式を全部分圏へ含める。
規約：元の図式と標的の全図式を同時に保つ。
使われ方：相対制限の零次元の境界充填。 -/
lemma kanRelativeJoinRelativeColimitRestriction_surjective {K C D E : SSet.{u}}
    [Quasicategory C] [Quasicategory D] [Quasicategory E]
    (p : K ⟶ C) [CocartesianFibration p] (U : D ⟶ E) (hU : SerrePositivity.InfinityCategories.F1B.EquivalenceLifting U)
    (sr : internalHom.PullbackObjObj (relativeJoinInl p (𝟙 C)) U)
    (hlocal : ∀ (F : K ⟶ D) (G : relativeJoin p (𝟙 C) ⟶ E),
      F ≫ U = relativeJoinInl p (𝟙 C) ≫ G → ∀ c : C _⦋0⦌,
        ∃ z : JoinCocone (vertexFiberι p c ≫ F), IsRelativeColimitCone U z ∧
          z.val ≫ U = (kanRelativeJoinFiberCocone p c G).val) :
    Function.Surjective
      ((kanRelativeJoinRelativeColimitRestriction p U sr).app (Opposite.op ⦋0⦌)) := by
  intro y
  obtain ⟨F, hF⟩ := (functorVertexEquiv K D).surjective (sr.fst.app (Opposite.op ⦋0⦌) y)
  obtain ⟨G, hG⟩ := (functorVertexEquiv (relativeJoin p (𝟙 C)) E).surjective
    (sr.snd.app (Opposite.op ⦋0⦌) y)
  have hFG : F ≫ U = relativeJoinInl p (𝟙 C) ≫ G := by
    have h := ConcreteCategory.congr_hom
      (NatTrans.congr_app sr.isPullback.w (Opposite.op ⦋0⦌)) y
    change ((ihom K).map U).app (Opposite.op ⦋0⦌) (sr.fst.app (Opposite.op ⦋0⦌) y) =
      ((pre (relativeJoinInl p (𝟙 C))).app E).app (Opposite.op ⦋0⦌)
        (sr.snd.app (Opposite.op ⦋0⦌) y) at h
    rw [← hF, ← hG] at h
    exact functorVertex_injective h
  obtain ⟨H, hHF, hHG, hHc⟩ :=
    exists_kanGlobalRelative_diagram_with_relative_colimits_of_lifting p U hU F G hFG
      (hlocal F G hFG)
  have hv : KanRelativeJoinRelativeColimitVertex p U (functorVertex H) := by
    intro c
    have he : (functorVertexEquiv (relativeJoin p (𝟙 C)) D).symm (functorVertex H) = H :=
      (functorVertexEquiv _ D).symm_apply_apply H
    rw [he]
    exact hHc c
  let x : (kanRelativeJoinRelativeColimitDiagrams p U : SSet.{u}) _⦋0⦌ :=
    ⟨functorVertex H, by
      intro α
      have hα : α = 𝟙 _ := Subsingleton.elim _ _
      simpa only [hα, op_id, Functor.map_id_apply] using hv⟩
  refine ⟨x, ?_⟩
  apply Types.ext_of_isPullback
    (sr.isPullback.map ((evaluation _ (Type u)).obj (Opposite.op ⦋0⦌)))
  · change (kanRelativeJoinRelativeColimitRestriction p U sr ≫ sr.fst).app
      (Opposite.op ⦋0⦌) x = sr.fst.app (Opposite.op ⦋0⦌) y
    rw [kanRelativeJoinRelativeColimitRestriction, Category.assoc, sr.π_fst]
    change functorVertex (relativeJoinInl p (𝟙 C) ≫ H) = sr.fst.app (Opposite.op ⦋0⦌) y
    rw [hHF]
    exact hF
  · change (kanRelativeJoinRelativeColimitRestriction p U sr ≫ sr.snd).app
      (Opposite.op ⦋0⦌) x = sr.snd.app (Opposite.op ⦋0⦌) y
    rw [kanRelativeJoinRelativeColimitRestriction, Category.assoc, sr.π_snd]
    change functorVertex (H ≫ U) = sr.snd.app (Opposite.op ⦋0⦌) y
    rw [hHG]
    exact hG

/-- 概要：局所相対余極限があれば相対普遍図式の全部分圏からの制限は自明 Kan。
方針：写像空間の充満忠実性、inner 性、頂点の厳密な全射性を合わせる。
規約：結論は h Fun の一意性より強い全境界の持ち上げ。
使われ方：相対 Kan 図式の coherent な構成と可縮な選択。 -/
lemma kanRelativeJoinRelativeColimitRestriction_trivialKanFibration {K C D E : SSet.{u}}
    [Quasicategory C] [Quasicategory D] [Quasicategory E]
    (p : K ⟶ C) [CocartesianFibration p] (U : D ⟶ E) (hU : SerrePositivity.InfinityCategories.F1B.EquivalenceLifting U)
    (sr : internalHom.PullbackObjObj (relativeJoinInl p (𝟙 C)) U)
    (hlocal : ∀ (F : K ⟶ D) (G : relativeJoin p (𝟙 C) ⟶ E),
      F ≫ U = relativeJoinInl p (𝟙 C) ≫ G → ∀ c : C _⦋0⦌,
        ∃ z : JoinCocone (vertexFiberι p c ≫ F), IsRelativeColimitCone U z ∧
          z.val ≫ U = (kanRelativeJoinFiberCocone p c G).val) :
    TrivialKanFibration (kanRelativeJoinRelativeColimitRestriction p U sr) := by
  have : InnerFibration U := hU.innerFibration
  have : Quasicategory sr.pt := kanRelativeInternalHomTarget_quasicategory U _ sr
  have : Quasicategory (kanRelativeJoinRelativeColimitDiagrams p U : SSet.{u}) :=
    inferInstanceAs (Quasicategory
      (fullSubcomplexOnVertices _ (KanRelativeJoinRelativeColimitVertex p U)))
  have : InnerFibration (kanRelativeJoinRelativeColimitRestriction p U sr) :=
    kanRelativeJoinRelativeColimitRestriction_innerFibration p U hU sr
  have hff : IsFullyFaithful (kanRelativeJoinRelativeColimitRestriction p U sr) :=
    kanRelativeJoinRelativeColimitRestriction_isFullyFaithful p U hU sr
  exact hff.trivialKanFibration_of_surjective
    (kanRelativeJoinRelativeColimitRestriction_surjective p U hU sr hlocal)

end SerrePositivity.InfinityCategories.F1B
