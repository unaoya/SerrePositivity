module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.Coherent
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.Walking
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.WalkingJoinCones

/-!
概要：強い分裂から、指定した同じ全 Idem 図式への元の錐と余錐を構成する。
方針：元の歩行図式の native な全錐を後合成し、元の制限の等式を使う。
規約：元の分裂頂点と二つの脚を保持する。普遍性は別に証明する。
使われ方：HTT 4.4.5.12〜14 の同じ冪等図式の余極限・極限による特徴づけ。

対応節は Kerodon 8.5（Tag 03Y9）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents

/-- 元の強い分裂から、指定した同じ全冪等図式への元の余錐を取り出す。 -/
def StrongSplitting.cocone {X : SSet.{u}} {d : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.CoherentIdempotent X}
    (s : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.StrongSplitting d) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone d :=
  ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.walkingJoinCocone.val ≫ s.val, by rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.walkingJoinCocone.property, s.property]⟩

/-- 元の強い分裂から、指定した同じ全冪等図式への元の錐を取り出す。 -/
def StrongSplitting.cone {X : SSet.{u}} {d : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.CoherentIdempotent X}
    (s : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.StrongSplitting d) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone d :=
  ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.walkingJoinCone.val ≫ s.val, by rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.walkingJoinCone.property, s.property]⟩

/-- 元の余錐の点側への制限は、元の分裂頂点そのもの。 -/
lemma StrongSplitting.cocone_point {X : SSet.{u}} {d : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.CoherentIdempotent X}
    (s : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.StrongSplitting d) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IdemShape (Δ[0] : SSet.{u}) ≫ s.cocone.val = SSet.yonedaEquiv.symm s.vertex := by
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IdemShape (Δ[0] : SSet.{u}) ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.walkingJoinCocone.val ≫ s.val) = _
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.walkingJoinCocone_point]
  apply SSet.yonedaEquiv.injective
  rw [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply]
  rfl

/-- 元の余錐の頂点は、元の強い分裂の指定した頂点そのもの。 -/
lemma StrongSplitting.cocone_vertex {X : SSet.{u}} {d : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.CoherentIdempotent X}
    (s : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.StrongSplitting d) : s.cocone.vertex = s.vertex := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone.vertex_eq, s.cocone_point, SSet.yonedaEquiv.apply_symm_apply]

/-- 元の錐の頂点も、元の強い分裂の同じ指定頂点そのもの。 -/
lemma StrongSplitting.cone_vertex {X : SSet.{u}} {d : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.CoherentIdempotent X}
    (s : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.StrongSplitting d) : s.cone.vertex = s.vertex := by
  change SSet.yonedaEquiv (_ ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.walkingJoinCone.val ≫ s.val)) = _
  rw [← Category.assoc, SSet.yonedaEquiv_comp]
  change s.val.app _ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.walkingJoinCone.vertex = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.walkingJoinCone_vertex]
  rfl

/-- 元の余錐の脚は、元の分裂図式の同じ射影辺。 -/
lemma StrongSplitting.cocone_leg {X : SSet.{u}} {d : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.CoherentIdempotent X}
    (s : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.StrongSplitting d) : s.cocone.val.app (Opposite.op ⦋1⦌)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.joinCoconeLegSimplex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.walkingObject)) =
        s.val.app (Opposite.op ⦋1⦌) (ComposableArrows.mk₁ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.walkingRetraction) := by
  change s.val.app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.walkingJoinCocone.val.app _ _) = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.walkingJoinCocone_leg]

/-- 元の錐の脚は、元の分裂図式の同じ包含辺。 -/
lemma StrongSplitting.cone_leg {X : SSet.{u}} {d : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.CoherentIdempotent X}
    (s : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.StrongSplitting d) : s.cone.val.app (Opposite.op ⦋1⦌)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coneLegSimplex _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.walkingObject) =
        s.val.app (Opposite.op ⦋1⦌) (ComposableArrows.mk₁ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.walkingSection) := by
  change s.val.app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.walkingJoinCone.val.app _ _) = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.walkingJoinCone_leg]

/-- 元の強い分裂の後合成と、元の全余錐の後合成は厳密に一致する。 -/
lemma StrongSplitting.cocone_map {X Y : SSet.{u}} {d : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.CoherentIdempotent X}
    (s : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.StrongSplitting d) (F : X ⟶ Y) : (s.map F).cocone.val = s.cocone.val ≫ F := by
  exact (Category.assoc _ _ _).symm

/-- 元の強い分裂の後合成と、元の全錐の後合成は厳密に一致する。 -/
lemma StrongSplitting.cone_map {X Y : SSet.{u}} {d : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.CoherentIdempotent X}
    (s : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.StrongSplitting d) (F : X ⟶ Y) : (s.map F).cone.val = s.cone.val ≫ F := by
  exact (Category.assoc _ _ _).symm

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents
