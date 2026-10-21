module

public import SerrePositivity.EInfinity.Hammock.FiniteQuiver
public import Mathlib.CategoryTheory.Localization.LocalizerMorphism

/-!
# 元の有限頂点自由圏から全自由圏への相対包含

概要：元の pathInclusion を全指定相対関手へ束ねる。
方針：元の生成辺と射列をそのまま射影する。
規約：quiver は有限頂点側だけ局所選択する。
使われ方：持ち上げた元の hammock grid の回収。
-/

@[expose] public section
universe u v
noncomputable section
namespace SerrePositivity.EInfinity.Hammock.FiniteQuiver
open CategoryTheory

variable {Q : Type u} [Quiver.{v} Q]

def pathRelative (S : Finset Q) : letI := quiver S
    LocalizerMorphism (⊤ : MorphismProperty (Paths (Vertex S)))
      (⊤ : MorphismProperty (Paths Q)) := by
  letI := quiver S
  exact ⟨pathInclusion S, fun _ _ _ _ => trivial⟩

end SerrePositivity.EInfinity.Hammock.FiniteQuiver
