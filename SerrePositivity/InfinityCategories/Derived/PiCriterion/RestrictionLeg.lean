module

public import SerrePositivity.InfinityCategories.F2.Compact.CoconeLegComposition
public import SerrePositivity.InfinityCategories.Stable.ColimitReindex

/-!
概要：底の制限に沿って、元の余錐の同じ脚の全辺を厳密に回収する。
方針：joinMap の合成と Yoneda の自然性を使う。
規約：辺の類の比較へ弱めない。頂点は定義上同じ。
使われ方：宇宙を上げた底から D の元の脚へ戻す。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.PiCriterion

/-- 底を制限した元の余錐の脚は、元の像の頂点の脚と同じ全一単体を持つ。 -/
lemma coconeTransportLeg_restrict_edge {A B X : SSet.{u}} {F : B ⟶ X}
    (c : JoinCocone F) (f : A ⟶ B) (a : A _⦋0⦌) :
    (Compact.coconeTransportLeg (c.restrict f) a).edge =
      (Compact.coconeTransportLeg c (f.app _ a)).edge := by
  rw [Compact.coconeTransportLeg_edge, Compact.coconeTransportLeg_edge]
  have hp : SSet.yonedaEquiv.symm a ≫ f = SSet.yonedaEquiv.symm (f.app _ a) := by
    apply SSet.yonedaEquiv.injective
    rw [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  change SSet.yonedaEquiv ((joinStdSimplexIso 0 0).inv ≫
      joinMap (SSet.yonedaEquiv.symm a) (𝟙 Δ[0]) ≫ (joinMap f (𝟙 Δ[0]) ≫ c.val)) = _
  rw [← Category.assoc (joinMap (SSet.yonedaEquiv.symm a) (𝟙 Δ[0])),
    ← joinMap_comp, Category.id_comp, hp]
  rfl

/-- 制限した余錐の同じ脚は、端点を含めて元の脚そのもの。 -/
lemma coconeTransportLeg_restrict {A B X : SSet.{u}} {F : B ⟶ X}
    (c : JoinCocone F) (f : A ⟶ B) (a : A _⦋0⦌) :
    Compact.coconeTransportLeg (c.restrict f) a =
      Compact.coconeTransportLeg c (f.app _ a) :=
  SSet.Edge.ext (coconeTransportLeg_restrict_edge c f a)

end SerrePositivity.InfinityCategories.F2.PiCriterion
