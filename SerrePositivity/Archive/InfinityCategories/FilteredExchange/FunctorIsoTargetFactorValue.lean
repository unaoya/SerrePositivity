module

public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.FunctorIsoTransport

/-!
概要：比較合成の第二因子だけへの終点等式の輸送は、元の合成の指定値を保持する。
方針：終点の等式を消去する。
規約：元の両因子を保持。使われ方：全三角形比較の終点表示の分配。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.F2

/-- 第二因子だけの終点表示の変更は、二つの元の指定比較の合成の値を保つ。 -/
lemma functorIso_trans_target_heq {X Y : SSet.{u}} {f g h h' : X ⟶ Y}
    (e : FunctorIso f g) (d : FunctorIso g h) (hh : h = h') :
    HEq (e ≪≫ functorIsoOfEq d rfl hh) (e ≪≫ d) := by
  subst h'
  rfl

end SerrePositivity.InfinityCategories.F2
