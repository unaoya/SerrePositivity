module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.PointedOppositeHomAction
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.PointedReverseKanDiagonalValue

/-!
概要：F1 の反対 Kan 圏の全豊穣合成と、元の全反転 Hom の合成を一致させる。
方針：宇宙持ち上げと反転の交換同型の単体上の作用を計算する。
規約：二つの独立係数を保持。使われ方：左区間輸送の値と元の指定作用の接続。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
namespace SerrePositivity.InfinityCategories.F2
open HomotopyLimits

/-- 反対 Kan の合成は係数の交換同型を戻すと元の全反転 Hom の合成そのもの。 -/
lemma pointedReverseKanHomComposition_normalized (K L : KanObject.{u}) :
    ((uliftOppositeIso (SimplicialCategory.sHom pointKanObject K)).hom ⊗ₘ
      (uliftOppositeIso (SimplicialCategory.sHom K L)).hom) ≫
      coherentReverseHomComposition (Opposite.op L) (Opposite.op K)
        (Opposite.op pointKanObject) ≫
      (uliftOppositeIso (SimplicialCategory.sHom pointKanObject L)).inv =
    (β_ ((SSet.uliftFunctor.{u + 1, u}).obj
      (SimplicialCategory.sHom pointKanObject K).op)
      ((SSet.uliftFunctor.{u + 1, u}).obj (SimplicialCategory.sHom K L).op)).hom ≫
      (uliftTensorIso (SimplicialCategory.sHom K L).op
        (SimplicialCategory.sHom pointKanObject K).op).inv ≫
      (SSet.uliftFunctor.{u + 1, u}).map (oppositeHomPrecomposition pointKanObject K L) := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro a
  rfl

end SerrePositivity.InfinityCategories.F2
