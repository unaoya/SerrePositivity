module

public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.QuiverTreeRootCategory
public import SerrePositivity.EInfinity.Hammock.SubsingletonCategoryContractible

/-!
# 根だけを含む有限部分木の実際の hammock の可縮性

概要：元の有限頂点の自由圏と全語の余極限をそのまま使う基底を示す。
方針：証明済みの対象と射の一意性を局所選択し、元の終射の弱同値性へ代入する。
規約：根だけの仮定は元の有限集合の全頂点について検査する。
使われ方：有限部分木の頂点数による帰納の基底。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.QuiverTree
open CategoryTheory SerrePositivity.InfinityCategories

variable {Q : Type u} [Quiver.{v} Q] (T : WideSubquiver (Quiver.Symmetrify Q))
  [Quiver.Arborescence T] [Quiver.IsThin (Quiver.FreeGroupoid Q)] {S : Finset Q}

lemma root_colimit_isWeaklyContractible
    (hroot : ∀ x ∈ S, (show T from x) = Quiver.root T) :
    letI := FiniteQuiver.quiver S
    ∀ x y : Paths (FiniteQuiver.Vertex S),
      IsWeaklyContractible (colimitGraph
        (⊤ : MorphismProperty (Paths (FiniteQuiver.Vertex S))) x y) := by
  let := FiniteQuiver.quiver S
  let := rootPathsSubsingleton T hroot
  let := rootPathsThin T hroot
  intro x y
  exact SubsingletonCategory.colimit_isWeaklyContractible _ x y

end SerrePositivity.EInfinity.Hammock.QuiverTree
