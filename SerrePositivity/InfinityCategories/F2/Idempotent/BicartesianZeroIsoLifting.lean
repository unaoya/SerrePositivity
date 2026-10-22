module

public import SerrePositivity.InfinityCategories.F2.Idempotent.BicartesianZeroBoundary
public import SerrePositivity.InfinityCategories.F1.FullSubcomplexEquivalenceLifting
public import SerrePositivity.InfinityCategories.F1B.KanEquivalenceLiftingInvertible

/-!
概要：元の双カルテジアン零角四角形の下辺射影は、元の全関手同型を厳密に持ち上げる。
方針：三条件の同型不変性から全部分圏の包含の持ち上げを得て、元の下辺制限と合成。
規約：元の下辺を厳密に回収する。標的の安定性や新しい普遍図式の存在を仮定しない。
使われ方：完備化の新しい辺への双普遍四角形の回収。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Idempotent

/-- 元の下辺射影は、全パラメータの可逆比較を境界固定で持ち上げる。 -/
lemma bicartesianZeroBottomProjection_kanEquivalenceLifting (X : SSet.{u}) [Quasicategory X] :
    F1B.KanEquivalenceLifting (bicartesianZeroBottomProjection X) := by
  have hi : F1B.KanEquivalenceLifting (fullSubcomplexOnVertices
      ((ihom ((Δ[1] : SSet.{u}) ⊗ Δ[1])).obj X) IsBicartesianZeroVertex).ι :=
    kanEquivalenceLifting_fullSubcomplexOnVertices_ι
    (IsBicartesianZeroVertex (X := X)) (fun e ↦
      ⟨fun h ↦ isBicartesianZeroVertex_of_retract (IsVertexRetractOf.of_iso e.symm) h,
        fun h ↦ isBicartesianZeroVertex_of_retract (IsVertexRetractOf.of_iso e) h⟩)
  have : Mono (squareBottomEdge.{u}) := by
    apply mono_of_mono_fac (show squareBottomEdge.{u} ≫ fst Δ[1] Δ[1] = 𝟙 Δ[1] from
      lift_fst _ _)
  have hp : F1B.KanEquivalenceLifting ((pre squareBottomEdge).app X) :=
    F1B.kanEquivalenceLifting_pre (X := X) squareBottomEdge
  intro A B i hm he
  have : HasLiftingProperty i (fullSubcomplexOnVertices
      ((ihom ((Δ[1] : SSet.{u}) ⊗ Δ[1])).obj X) IsBicartesianZeroVertex).ι := hi i hm he
  have : HasLiftingProperty i ((pre squareBottomEdge).app X) := hp i hm he
  unfold bicartesianZeroBottomProjection
  infer_instance

end SerrePositivity.InfinityCategories.F2.Idempotent
