module
public import SerrePositivity.InfinityCategories.Derived.RoofReverseVertexEdge
public import SerrePositivity.InfinityCategories.F1B.NerveComparison.OverIso

/-! # 通常の屋根の反対頂点と構造辺

概要：Over の反対 Under 表示の零単体と、Under の構造辺を元の指定射で評価する。
方針：零次の射列の外延性と、点の join の両逆性を使う。
規約：対象や射を選び直さない。使われ方：over 比較の頂点における辺の回収。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory Opposite SSet
open scoped Simplicial
variable {C : Type u} [Category.{u} C]

/-- Over の零単体を反対 Under の指定零単体へ送る。 -/
lemma ordinaryRoofOppositeVertex (c : C) (s : Over c) :
    (SerrePositivity.InfinityCategories.F1B.nerveOverOppositeUnderIso c).hom.app (Opposite.op ⦋0⦌) (nerveVertex s) =
      SSet.opObjEquiv.symm (nerveVertex ((Under.opEquivOpOver c).inverse.obj (op s))) := by
  apply SSet.opObjEquiv.injective
  exact ComposableArrows.ext₀ rfl

/-- Under の指定零単体の辺は、その指定構造射。 -/
lemma ordinaryUnderVertexEdge (c : C) (s : Under c) :
    SSet.yonedaEquiv ((joinStdSimplexIso 0 0).inv ≫
      (SerrePositivity.InfinityCategories.F1B.nerveUnderSimplex c (nerveVertex s)).val) = ComposableArrows.mk₁ s.hom := by
  change SSet.yonedaEquiv ((joinStdSimplexIso 0 0).inv ≫
    ((pointJoinStdSimplexIso 0).hom ≫ (SSet.yonedaEquiv (X := nerve C)).symm
      (SerrePositivity.InfinityCategories.F1B.nerveUnderChain c (nerveVertex s)))) = _
  have hi : pointJoinStdSimplexIso.{u} 0 = joinStdSimplexIso 0 0 := by
    apply Iso.ext
    rfl
  rw [hi, Iso.inv_hom_id_assoc, Equiv.apply_symm_apply]
  refine ComposableArrows.ext₁ (F := SerrePositivity.InfinityCategories.F1B.nerveUnderChain c (nerveVertex s))
    (G := ComposableArrows.mk₁ s.hom) rfl rfl ?_
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  rfl

end SerrePositivity.InfinityCategories
