module

public import SerrePositivity.InfinityCategories.F2.CatInfinity.CatPullbackConeLeftImagePath
public import SerrePositivity.InfinityCategories.F2.CatInfinity.CatPullbackConeRightImageProjection
public import SerrePositivity.InfinityCategories.Core.CatInfinity.VertexIsoTerminalEquality

/-!
概要：native な極限錐と二射影・指定可逆 path の同時比較。
方針：左右の像の整合式に指定射影への比較を合成する。
規約：指定された三角形と同型の値を保持する。
使われ方：引き戻し錐と指定 path の比較を簡約する。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u v
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

variable {A B C : SSet.{u}} [Quasicategory A] [Quasicategory B] [Quasicategory C]
/-- 概要：native な極限錐と二射影・指定可逆 path の同時比較。
方針：左右の像の整合式に指定射影への比較を合成する。
規約：元の指定同型の値と合成の向きを保持する。
使われ方：Cat_∞ 内の引き戻しと全試験関手 core の比較。 -/
lemma catPullbackCone_projection_commutativity (p : A ⟶ C) (q : B ⟶ C) :
    (catPullbackConeFstIso p q).postcomp p ≪≫ catPullbackCommutativity p q =
      catPullbackConeNativeCommutativity p q ≪≫ (catPullbackConeSndIso p q).postcomp q := by
  unfold catPullbackCommutativity
  rw [← functorEqIso_eqToIso
      (pullback.condition (f := equivalencePathReplacementMap p) (g := q)),
    ← Iso.trans_assoc, catPullbackConeLeftImageIso_path,
    ← catPullbackConeImageIso_commutativity, Iso.trans_assoc,
    catPullbackConeRightImageIso_projection]

end SerrePositivity.InfinityCategories.F2
