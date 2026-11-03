module

public import SerrePositivity.InfinityCategories.Core.Cocone
public import SerrePositivity.InfinityCategories.Core.EquivalenceLimits
public import SerrePositivity.InfinityCategories.Core.Join
public import SerrePositivity.InfinityCategories.Core.Limit
public import SerrePositivity.InfinityCategories.Core.Pullback
public import SerrePositivity.InfinityCategories.Core.PushoutShape
public import SerrePositivity.InfinityCategories.Core.Square
public import SerrePositivity.InfinityCategories.F1B.KanExtension.RelativeCoconeAbsolute
public import SerrePositivity.InfinityCategories.Core.CatInfinity.CoconeValEquality
public import SerrePositivity.InfinityCategories.Core.CatInfinity.ConeValEquality

/-!
概要：四角形の後合成と指定された極限錐・余極限余錐の一致。
方針：四角形と join の同型を用いた全錐の射の合成則を計算する。
規約：元の四角形と関手を保持する。
使われ方：lax pullback の成分判定を四角形へ移す。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 概要：引き戻し錐の後合成の極限性は像の四角形の引き戻し性と同値。
方針：元の錐と像の四角形の錐の全射の等式を使う。
規約：像の図式の括弧付けを厳密な合成則で照合する。
使われ方：射影の四角形保存と反映。 -/
lemma isLimitCone_map_pullbackCone_iff {X Y : SSet.{u}} (f : X ⟶ Y)
    (R : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ X) :
    IsLimitCone (mapJoinCone f (pullbackCone R)) ↔ IsPullbackSquare (R ≫ f) := by
  apply isLimitCone_iff_of_cone_val_eq
  change (cospanConeSquareIso.hom ≫ R) ≫ f = cospanConeSquareIso.hom ≫ (R ≫ f)
  exact Category.assoc _ _ _

/-- 概要：押し出し余錐の後合成の余極限性は像の四角形の押し出し性と同値。
方針：元の余錐と像の四角形の余錐の全射の等式を使う。
規約：元の全余錐を同型類に置き換えない。
使われ方：完全関手の余極限保存を錐の保存へ移す。 -/
lemma isColimitCone_post_pushoutCocone_iff {X Y : SSet.{u}} (f : X ⟶ Y)
    (R : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ X) :
    IsColimitCone (F1B.kanPostcomposeCocone f (pushoutCocone R)) ↔
      IsPushoutSquare (R ≫ f) := by
  apply isColimitCone_iff_of_cocone_val_eq
  change (spanCoconeSquareIso.hom ≫ R) ≫ f = spanCoconeSquareIso.hom ≫ (R ≫ f)
  exact Category.assoc _ _ _

end SerrePositivity.InfinityCategories.F2
