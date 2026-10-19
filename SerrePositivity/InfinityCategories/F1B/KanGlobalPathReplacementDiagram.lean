module

public import SerrePositivity.InfinityCategories.F1B.KanRelativeColimitPathReplacement
public import SerrePositivity.InfinityCategories.F1B.KanGlobalLiftingDiagram

/-!
概要：一般の関手上の相対 Kan 図式を指定された可逆 path とともに組み立てる。
方針：定値 path の切断で局所余錐を置換へ移し、組み立て後に元の始域へ射影する。
規約：標的図式との比較 path は元の指定部分では定値。
使われ方：isofibration 上での厳密化に先立つ相対 Kan 図式の構成。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F1B

/-- 概要：局所相対余極限から標的への可逆 path つきの大域相対図式を構成する。
方針：path 置換は右持ち上げ条件を持つため、局所余錐を切断で移して組み立てる。
規約：U に充填性を要求しない。元の図式を厳密に保ち、比較 path はそこで定値。
使われ方：相対 Kan 拡張の因子分解による存在証明の厳密化前の段階。 -/
lemma exists_kanGlobalRelative_diagram_with_equivalencePath
    {K C D E : SSet.{u}} [Quasicategory C] [Quasicategory D] [Quasicategory E]
    (p : K ⟶ C) [CocartesianFibration p] (U : D ⟶ E) (F : K ⟶ D)
    (H₀ : relativeJoin p (𝟙 C) ⟶ E)
    (hFU : F ≫ U = relativeJoinInl p (𝟙 C) ≫ H₀)
    (hlocal : ∀ c : C _⦋0⦌, ∃ z : JoinCocone (vertexFiberι p c ≫ F),
      IsRelativeColimitCone U z ∧ z.val ≫ U = (kanRelativeJoinFiberCocone p c H₀).val) :
    ∃ (H : relativeJoin p (𝟙 C) ⟶ D)
      (P : relativeJoin p (𝟙 C) ⟶ equivalencePath E),
      relativeJoinInl p (𝟙 C) ≫ H = F ∧
      P ≫ equivalencePathEndpoint E 0 = H ≫ U ∧
      P ≫ equivalencePathEndpoint E 1 = H₀ ∧
      relativeJoinInl p (𝟙 C) ≫ P = F ≫ U ≫ equivalencePathRefl E ∧
      ∀ c : C _⦋0⦌, IsRelativeColimitCone U (kanRelativeJoinFiberCocone p c H) := by
  let s := equivalencePathReplacementSection U
  let q := equivalencePathReplacementMap U
  let r := equivalencePathReplacementProjection U
  have hs : s ≫ q = U := equivalencePathReplacementSection_map U
  have hsr : s ≫ r = 𝟙 D := equivalencePathReplacementSection_projection U
  have hl : ∀ c : C _⦋0⦌, ∃ z : JoinCocone (vertexFiberι p c ≫ F ≫ s),
      IsRelativeColimitCone q z ∧ z.val ≫ q = (kanRelativeJoinFiberCocone p c H₀).val := by
    intro c
    obtain ⟨z, hz, hzu⟩ := hlocal c
    let z' : JoinCocone (vertexFiberι p c ≫ F ≫ s) :=
      (sliceUnderPostcomp (vertexFiberι p c ≫ F) s).app (Opposite.op ⦋0⦌) z
    have hbase : (vertexFiberι p c ≫ F ≫ s) ≫ r = vertexFiberι p c ≫ F := by
      rw [Category.assoc, Category.assoc, hsr, Category.comp_id]
    have he : ((sliceUnderPostcomp (vertexFiberι p c ≫ F ≫ s) r).app
        (Opposite.op ⦋0⦌) z').val = z.val := by
      change (z.val ≫ s) ≫ r = z.val
      rw [Category.assoc, hsr, Category.comp_id]
    refine ⟨z', ?_, ?_⟩
    · apply (kanIsRelativeColimitCone_equivalencePathReplacement_iff U z').2
      exact (kanIsRelativeColimitCone_congr U hbase _ z he).2 hz
    · change (z.val ≫ s) ≫ q = _
      rw [Category.assoc, hs]
      exact hzu
  obtain ⟨L, hLF, hLq, hLc⟩ :=
    exists_kanGlobalRelative_diagram_with_relative_colimits_of_lifting p q
      (kanEquivalenceLifting_equivalencePathReplacementMap U) (F ≫ s) H₀
      (by rw [Category.assoc, hs]; exact hFU) hl
  let H := L ≫ r
  let P := L ≫ pullback.fst (equivalencePathEndpoint E 0) U
  refine ⟨H, P, ?_, ?_, ?_, ?_, ?_⟩
  · change relativeJoinInl p (𝟙 C) ≫ L ≫ r = F
    rw [← Category.assoc, hLF, Category.assoc, hsr, Category.comp_id]
  · change L ≫ pullback.fst (equivalencePathEndpoint E 0) U ≫
      equivalencePathEndpoint E 0 = (L ≫ r) ≫ U
    rw [pullback.condition, Category.assoc]
    rfl
  · exact hLq
  · change relativeJoinInl p (𝟙 C) ≫ L ≫
      pullback.fst (equivalencePathEndpoint E 0) U = _
    rw [← Category.assoc, hLF, Category.assoc]
    change F ≫ (pullback.lift (U ≫ equivalencePathRefl E) (𝟙 D) _ ≫
      pullback.fst (equivalencePathEndpoint E 0) U) = _
    rw [pullback.lift_fst]
  · intro c
    have hc := (kanIsRelativeColimitCone_equivalencePathReplacement_iff U
      (kanRelativeJoinFiberCocone p c L)).1 (hLc c)
    exact hc

end SerrePositivity.InfinityCategories.F1B
