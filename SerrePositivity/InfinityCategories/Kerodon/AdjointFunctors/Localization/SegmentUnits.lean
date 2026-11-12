module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Segment

/-!
# 空区間の合成は元の恒等射

概要：語の写像の空 fiber に挿入される区間合成を、元の恒等射と同定する。
方針：零個の列の両端は同じであり、合成可能射列の関手性から従う。
規約：恒等射は局所化後だけでなく元の圏での等式。
使われ方：語の作用の単位・恒等列の挿入。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open CategoryTheory

variable {C : Type u} [Category.{v} C] {W : MorphismProperty C} {w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} {X Y : C}

/-- 空の連続区間の合成は、元の同じ頂点の恒等射。 -/
lemma map_refl (d : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Direction) (S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W w X Y) (p : Fin (w.length + 1))
    (hd : ∀ i : Fin w.length, p.val ≤ i.val → i.val < p.val → w.direction i = d) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Segment.map d S p p le_rfl hd = 𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DirectionCategory.vertex d (S.vertex p)) := by
  let F := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Segment.chain d S p p le_rfl hd
  have hz : (0 : Fin (p.val - p.val + 1)) = Fin.last (p.val - p.val) := by
    apply Fin.ext
    simp
  have hm : F.hom = eqToHom (congrArg F.obj hz) := by
    calc
      F.hom = F.map (eqToHom hz) := congrArg F.map (Subsingleton.elim _ _)
      _ = _ := eqToHom_map F hz
  change eqToHom _ ≫ F.hom ≫ eqToHom _ = 𝟙 _
  rw [hm, eqToHom_trans, eqToHom_trans]
  rfl

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
