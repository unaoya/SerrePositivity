module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCoverLiftTo

/-!
# 元の図式の持ち上げ頂点のラベル

概要：元の自由圏の図式の各頂点に根からの groupoid 射を指定する。
方針：各図式の射とラベルの右合成の等式を保持する。
規約：図式の対象・射を変更しない。
使われ方：元の hammock の部分射列の値から全図式を持ち上げる。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u v u' v'
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open CategoryTheory

variable {Q : Type u} [Quiver.{v} Q] (A : Q) {D : Type u'} [Category.{v'} D]

structure DiagramLabels (F : D ⥤ Paths Q) where
  path : ∀ d, (Quiver.FreeGroupoid.of Q).obj A ⟶
    (Quiver.FreeGroupoid.of Q).obj (show Q from F.obj d)
  naturality : ∀ {d e} (f : d ⟶ e), path d ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.positiveEvaluation.map (F.map f) = path e

def DiagramLabels.vertex {F : D ⥤ Paths Q} (L : DiagramLabels A F) (d : D) : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCover.Vertex A :=
  ⟨F.obj d, L.path d⟩

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
