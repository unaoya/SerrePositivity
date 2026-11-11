module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.ConeFamilyTensorComponents

/-!
概要：直積内の図式の錐族と成分ごとの錐族の直積との同型。
方針：二射影による後合成と二成分からの lift を互いに逆と示す。
規約：指定錐の頂点を元の両射影の錐の頂点と同定する。
使われ方：直積の成分ごとの極限錐判定。

対応節は Kerodon 5.5（Tag 01YV）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC

/-- 概要：直積の錐族は両成分の錐族の直積と同型。
方針：二射影を並べた射と成分の lift の往復を外延性で判定する。
規約：元の図式を全パラメータで固定する。
使われ方：両成分の終対象性から元の錐の極限性を得る。 -/
def coneFamilyTensorIso {J X Y : SSet.{u}} (r : J ⟶ X ⊗ Y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coneFamily r ≅ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coneFamily (r ≫ fst X Y) ⊗ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coneFamily (r ≫ snd X Y) where
  hom := CartesianMonoidalCategory.lift
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coneFamilyPostcomp r (fst X Y)) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coneFamilyPostcomp r (snd X Y))
  inv := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coneFamilyTensorLift r (fst _ _) (snd _ _)
  hom_inv_id := by
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coneFamilyTensor_hom_ext r
    · rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coneFamilyTensorLift_fst, lift_fst, Category.id_comp]
    · rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coneFamilyTensorLift_snd, lift_snd, Category.id_comp]
  inv_hom_id := by
    apply CartesianMonoidalCategory.hom_ext
    · rw [Category.assoc, lift_fst, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coneFamilyTensorLift_fst, Category.id_comp]
    · rw [Category.assoc, lift_snd, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coneFamilyTensorLift_snd, Category.id_comp]

/-- 概要：比較同型は指定錐を元の二射影による錐の組へ送る。
方針：二つの錐族の後合成の零次成分を計算する。
規約：同型類ではなく実際の指定頂点の等式。
使われ方：成分ごとの極限錐判定の頂点照合。 -/
lemma coneFamilyTensorIso_vertex {J X Y : SSet.{u}} (r : J ⟶ X ⊗ Y) (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone r) :
    (coneFamilyTensorIso r).hom.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coneFamilyVertexEquiv r c) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coneFamilyVertexEquiv (r ≫ fst X Y) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCone (fst X Y) c),
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coneFamilyVertexEquiv (r ≫ snd X Y) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCone (snd X Y) c)) := by
  apply Prod.ext
  · have h : (coneFamilyTensorIso r).hom ≫ fst _ _ =
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coneFamilyPostcomp r (fst X Y) := lift_fst _ _
    have hh := congrArg (fun f ↦ f.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coneFamilyVertexEquiv r c)) h
    exact hh.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coneFamilyPostcomp_vertex r (fst X Y) c)
  · have h : (coneFamilyTensorIso r).hom ≫ snd _ _ =
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coneFamilyPostcomp r (snd X Y) := lift_snd _ _
    have hh := congrArg (fun f ↦ f.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coneFamilyVertexEquiv r c)) h
    exact hh.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coneFamilyPostcomp_vertex r (snd X Y) c)

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
