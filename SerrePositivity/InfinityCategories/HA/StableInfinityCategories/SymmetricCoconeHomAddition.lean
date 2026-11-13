module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SymmetricCoconeHomProductNaturality
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.RepresentableAdditionCover
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.HomotopyPreadditive

/-! # 対称余錐空間から移した Hom の演算と既存の加法

概要：安定 ∞ 圏では対称 span の Hom のループ演算は既存の双積の加法に一致し、二枝交換は負の恒等射となる。
方針：全対象の頂点表示と自然な零単位演算の加法判定を使い、右逆元の公式を負号へ移す。
規約：既存の preadditive_ho の構造を用いる。使われ方：懸垂の交換自己同型の符号の同定。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories
section
variable {X : SSet.{u}} [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X]
local instance : Preadditive X.HomotopyCategory := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.preadditive_ho (X := X)
local instance : HasBinaryBiproducts X.HomotopyCategory := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.hasBinaryBiproducts_ho (X := X)

/-- 概要：余錐空間から移した Hom のループ演算は、既存の前加法構造の加法と一致する。
方針：各終点で枝の基点を選び、零単位と後合成自然性を全射的な頂点表示の一般判定へ与える。
規約：任意の基点に対して同じ等号。使われ方：二枝交換の右逆元を負号として読む。 -/
lemma symmetricCoconeHomProduct_eq_add {x z : X _⦋0⦌}
    (f : SSet.Truncated.Edge (X := (truncation 2).obj X) x z) (hz : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex z)
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.edgeSpan f f)) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c) (y : X _⦋0⦌)
    (e : (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace (SSet.yonedaEquiv.symm f.edge) y) _⦋0⦌)
    (u v : (SSet.HomotopyCategory.mk c.vertex : hoFunctor.obj X) ⟶ SSet.HomotopyCategory.mk y) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.symmetricCoconeHomProduct f hz c hc y e u v = u + v := by
  let ep (t : X _⦋0⦌) : (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace (SSet.yonedaEquiv.symm f.edge) t) _⦋0⦌ :=
    Classical.choice ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.coconeMappingSpace_edge_isContractibleKan _
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stableEdgeSimplex_target_initial f hz.1) t).nonempty)
  let μ := fun t => _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.symmetricCoconeHomProduct f hz c hc t (ep t)
  have hobj : Function.Surjective
      (fun t : X _⦋0⦌ => (SSet.HomotopyCategory.mk t : X.HomotopyCategory)) :=
    SSet.Truncated.HomotopyCategory.mk_surjective
  have h := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.representableOperation_eq_add_of_surjective_objects
    (C := X.HomotopyCategory) (fun t : X _⦋0⦌ => SSet.HomotopyCategory.mk t)
    hobj (SSet.HomotopyCategory.mk c.vertex) μ
    (fun t w => _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.symmetricCoconeHomProduct_zero_left f hz c hc t (ep t) w)
    (fun t w => _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.symmetricCoconeHomProduct_zero_right f hz c hc t (ep t) w)
    (fun t t' w w' h => _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.symmetricCoconeHomProduct_naturality f hz c hc t t'
      (ep t) (ep t') w w' h) y u v
  exact (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.symmetricCoconeHomProduct_basepoint f hz c hc y e (ep y) u v).trans h

/-- 概要：対称 span の二枝交換の余極限頂点自己同型は負の恒等射。
方針：恒等射に対する演算の右逆元の式を加法へ移し、加法消去する。
規約：余極限余錐は任意の選択。使われ方：対称な懸垂模型の交換の符号。 -/
lemma fixedCoconeSwap_eq_neg_id {x z : X _⦋0⦌}
    (f : SSet.Truncated.Edge (X := (truncation 2).obj X) x z) (hz : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex z)
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.edgeSpan f f)) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c) :
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.fixedCoconeReindexVertexIso c hc _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.spanSwap (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.edgeSpan_self_swap f) _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.spanSwap_comp_self).hom =
      -𝟙 (SSet.HomotopyCategory.mk c.vertex : hoFunctor.obj X) := by
  obtain ⟨e⟩ := (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.coconeMappingSpace_edge_isContractibleKan _
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stableEdgeSimplex_target_initial f hz.1) c.vertex).nonempty
  have h := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.symmetricCoconeHomProduct_swap f hz c hc c.vertex e (𝟙 _)
  rw [symmetricCoconeHomProduct_eq_add, Category.comp_id] at h
  apply add_left_cancel (a := 𝟙 (SSet.HomotopyCategory.mk c.vertex : hoFunctor.obj X))
  rw [add_neg_cancel]
  exact h

end
end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
