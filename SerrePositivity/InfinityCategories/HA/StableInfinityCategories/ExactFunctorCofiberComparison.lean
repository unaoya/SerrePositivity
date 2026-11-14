module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExactFunctorSuspension
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.CofiberComparisonComposition

/-! # 完全関手と指定懸垂への cofiber 比較

概要：完全関手は cofiber 列から指定した懸垂四角形への比較と、その接続射を保つ。
方針：四角形の h の射の始点成分による一意性を使う。
規約：懸垂四角形も元の四角形と一緒に写す。使われ方：三角関手の第三射の照合。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

/-- 概要：四角形の後合成の h の射を角で評価すると、その角の射の像になる。
方針：内部 Hom の後合成と評価の定義を計算する。
規約：始域 X は quasicategory。使われ方：比較の始点と終点の保存。 -/
lemma squareDiagramHoEvaluation_postcomp {X Y : SSet.{u}} [Quasicategory X] (F : X ⟶ Y)
    {a b : hoFunctor.obj ((ihom (Δ[1] ⊗ Δ[1] : SSet.{u})).obj X)} (f : a ⟶ b)
    (i j : Fin 2) :
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareDiagramHoEvaluation Y i j).map
      ((hoFunctor.map ((ihom (Δ[1] ⊗ Δ[1] : SSet.{u})).map F)).toFunctor.map f) =
      (hoFunctor.map F).toFunctor.map ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareDiagramHoEvaluation X i j).map f) := by
  unfold _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareDiagramHoEvaluation
  rw [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stableHoMap_comp, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stableHoMap_comp]
  rfl

/-- 概要：完全関手は始点を固定した cofiber から懸垂への標準比較を保つ。
方針：始点成分の計算と比較の一意性を使う。
規約：h の四角形の関手圏での等式。使われ方：接続射の像の計算。 -/
lemma cofiberSuspensionComparisonHom_postcomp {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] (F : X ⟶ Y) [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor F]
    (t : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.ZeroTriangle X) (ht : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsCofiberSequence t)
    (s : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SuspensionSquare (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex t.square 0 0)) :
    (hoFunctor.map ((ihom (Δ[1] ⊗ Δ[1] : SSet.{u})).map F)).toFunctor.map
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberSuspensionComparisonHom t.square ht s) =
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberSuspensionComparisonHom (t.square ≫ F)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor.preservesCofiber (F := F) t ht) (s.map F) := by
  apply _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberSuspensionComparison_hom_ext (t.square ≫ F)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor.preservesCofiber (F := F) t ht) (s.map F)
  change (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareDiagramHoEvaluation Y 0 0).map _ = (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareDiagramHoEvaluation Y 0 0).map _
  rw [squareDiagramHoEvaluation_postcomp, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberSuspensionComparisonHom_source,
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberSuspensionComparisonHom_source]
  simp only [eqToHom_map]

/-- 概要：指定懸垂への cofiber 接続射の像は、写した懸垂への接続射。
方針：標準比較の保存を終点で評価する。
規約：両側の h の零射構造は任意。使われ方：Σ に値を持つ接続射への橋渡し。 -/
lemma cofiberConnectingToSuspension_postcomp {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y]
    [Limits.HasZeroMorphisms (hoFunctor.obj X)] [Limits.HasZeroMorphisms (hoFunctor.obj Y)]
    (F : X ⟶ Y) [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor F] (t : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.ZeroTriangle X) (ht : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsCofiberSequence t)
    (s : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SuspensionSquare (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex t.square 0 0)) :
    (hoFunctor.map F).toFunctor.map (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberConnectingToSuspension t ht s) =
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberConnectingToSuspension (t.map F (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor.preservesZero (F := F)))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor.preservesCofiber (F := F) t ht) (s.map F) := by
  have h := congrArg ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareDiagramHoEvaluation Y 1 1).map)
    (cofiberSuspensionComparisonHom_postcomp F t ht s)
  rw [squareDiagramHoEvaluation_postcomp,
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberSuspensionComparisonHom_target t ht s] at h
  exact h.trans (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberSuspensionComparisonHom_target
    (t.map F (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor.preservesZero (F := F)))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor.preservesCofiber (F := F) t ht) (s.map F))

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
