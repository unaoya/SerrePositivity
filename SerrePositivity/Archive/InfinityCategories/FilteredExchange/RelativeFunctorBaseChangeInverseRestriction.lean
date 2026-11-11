module

public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.RelativeFunctorBaseChangeNaturality
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.VertexIsoMapCoherence
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.VertexIsoTerminalEquality

/-!
概要：相対写像空間の底変換の逆射は指定された始域制限と厳密に可換する。
方針：順方向の自然性を両側の同型で消去し、同じ等式で指定頂点同型を写す。
規約：底変換の逆を選び直さない。使われ方：終点比較の fiber 制限を元の作用へ戻す。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {E B D : SSet.{u}} (p : E ⟶ B) (k : D ⟶ B)
  {a b : Over D} (f : a ⟶ b)

/-- 既存の底変換同型の逆射と始域の前合成の厳密な交換式。 -/
lemma relativeFunctorBaseChangeInverse_overPre :
    relativeFunctorOverPre p ((Over.map k).map f) ≫
        (relativeFunctorBaseChangeIso p k a.hom).inv =
      (relativeFunctorBaseChangeIso p k b.hom).inv ≫
        relativeFunctorOverPre (pullback.snd p k) f := by
  apply (cancel_epi (relativeFunctorBaseChangeIso p k b.hom).hom).1
  apply (cancel_mono (relativeFunctorBaseChangeIso p k a.hom).hom).1
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id, Iso.hom_inv_id_assoc]
  exact (relativeFunctorBaseChangeForward_overPre p k f).symm

/-- 指定頂点同型を底変換の逆と始域制限で写す二通りの値は一致する。 -/
lemma relativeFunctorBaseChangeInverse_vertexIso_overPre
    {x y : (relativeFunctorSpace p (b.hom ≫ k)) _⦋0⦌} (e : VertexIso x y) :
    HEq
      (VertexIso.map (VertexIso.map e (relativeFunctorOverPre p ((Over.map k).map f)))
        (relativeFunctorBaseChangeIso p k a.hom).inv)
      (VertexIso.map (VertexIso.map e (relativeFunctorBaseChangeIso p k b.hom).inv)
        (relativeFunctorOverPre (pullback.snd p k) f)) := by
  exact (heq_of_eq (vertexIso_map_comp e
    (relativeFunctorOverPre p ((Over.map k).map f))
    (relativeFunctorBaseChangeIso p k a.hom).inv)).trans
      ((vertexIso_map_heq e (relativeFunctorBaseChangeInverse_overPre p k f)).trans
        (heq_of_eq (vertexIso_map_comp e (relativeFunctorBaseChangeIso p k b.hom).inv
          (relativeFunctorOverPre (pullback.snd p k) f))).symm)

end SerrePositivity.InfinityCategories.F2
