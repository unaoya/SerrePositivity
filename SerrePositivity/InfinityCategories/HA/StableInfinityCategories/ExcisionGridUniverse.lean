module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridSuspensionCorners
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.UniverseSquareHom

/-!
概要：切除格子の全単体と指定された四角形を別の宇宙へ持ち上げる。
方針：同じ有限順序集合の ULift を比較し、入力面と懸垂面を照合する。
規約：元の圏の有限余極限を大きい宇宙の仮定に置き換えない。
使われ方：表現可能前層を標的とする loop 同値の切除判定。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet MonoidalCategory
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

/-- 概要：大きい格子を元の小さい格子へ戻す通常関手。
方針：ULift の同じ有限順序成分を保つ。
規約：順序と各射を保つ。使われ方：格子の宇宙同型。 -/
def excisionGridUniverseDown : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridIndex.{u + 1} ⥤
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridIndex.{u} :=
  (show _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridIndex.{u + 1} →o _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridIndex.{u} from
    ⟨fun p ↦ ULift.up p.down, fun _ _ h ↦ h⟩).toFunctor

/-- 概要：小さい格子を同じ有限順序成分で大きい格子へ送る。
方針：ULift の宇宙だけを変更する。
規約：全順序関係を保持する。使われ方：格子の宇宙同型の逆。 -/
def excisionGridUniverseUp : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridIndex.{u} ⥤
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridIndex.{u + 1} :=
  (show _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridIndex.{u} →o _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridIndex.{u + 1} from
    ⟨fun p ↦ ULift.up p.down, fun _ _ h ↦ h⟩).toFunctor

/-- 概要：大きい切除格子と元の小さい格子の持ち上げは厳密に同型。
方針：全単体を同じ有限鎖として比較する。
規約：頂点だけでなく全射を保持する。使われ方：空間値切除の入力。 -/
def excisionGridUniverseIso : nerve _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridIndex.{u + 1} ≅
    (SSet.uliftFunctor.{u + 1, u}).obj (nerve _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridIndex.{u}) where
  hom := {
    app _ := ↾fun s ↦ ULift.up (s ⋙ excisionGridUniverseDown)
    naturality := by
      intro n m α
      rfl }
  inv := {
    app _ := ↾fun s ↦ s.down ⋙ excisionGridUniverseUp
    naturality := by
      intro n m α
      rfl }
  hom_inv_id := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro s
    apply CategoryTheory.Functor.ext
    · intro _ _ _; apply Subsingleton.elim
    · intros; rfl
  inv_hom_id := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro s
    apply ULift.ext
    apply CategoryTheory.Functor.ext
    · intro _ _ _; apply Subsingleton.elim
    · intros; rfl

/-- 概要：宇宙比較は元の入力四角形を厳密に保つ。
方針：標準単体の全鎖の同じ座標を計算する。
規約：入力面の向きを変えない。使われ方：切除の結論の読み戻し。 -/
lemma excisionGridUniverseIso_square :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridSquareEmbedding.{u + 1} ≫ excisionGridUniverseIso.hom =
      _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftSquareIso.{u, u + 1}.inv ≫
        (SSet.uliftFunctor.{u + 1, u}).map _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridSquareEmbedding.{u} := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro s
  apply ULift.ext
  apply CategoryTheory.Functor.ext
  · intro _ _ _; apply Subsingleton.elim
  · intros; rfl

/-- 概要：宇宙比較は四つの懸垂面をそれぞれ保つ。
方針：同じ二つのパラメーターと全単体の座標を照合する。
規約：面の添字を交換しない。使われ方：表現可能前層の極限保存。 -/
lemma excisionGridUniverseIso_suspension (i j : Fin 2) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridSuspensionAt.{u + 1} i j ≫ excisionGridUniverseIso.hom =
      _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftSquareIso.{u, u + 1}.inv ≫
        (SSet.uliftFunctor.{u + 1, u}).map (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridSuspensionAt.{u} i j) := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro s
  apply ULift.ext
  apply CategoryTheory.Functor.ext
  · intro _ _ _; apply Subsingleton.elim
  · intros; rfl

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
