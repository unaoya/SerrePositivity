module
public import SerrePositivity.InfinityCategories.Derived.Gluing.LaxHomPinchedIntervalTransport
/-!
概要：元の正本 lax Hom 引き戻しは Kan 複体である。
方針：F2 の矢印両端評価の Hom fibration を、元の二入力の Kan 複体上で引き戻す。
規約：追加のモデル圏仮定を置かず、元の pinched 標的を使う。
使われ方：正本比較の同値性を実ホモトピー逆と往復則へ戻す。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits MonoidalCategory DifferentialGraded DGNerve SSet
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D) (X Y : DGGluingObject R C D M)
lemma dgGluingLaxHomPullback_kanComplex :
    KanComplex (dgGluingLaxHomPullback R C D M X Y) := by
  let Z := (SSet.uliftFunctor.{max (u + 1) v w,max (u + 1) v}).obj
    (dgModuleDerivedInfinityCategory R C)
  letI : Quasicategory Z := inferInstance
  letI := F2.quasicategory_tensor Z Z
  letI := F2.quasicategory_tensor
    ((SSet.uliftFunctor.{max (u + 1) v w,max u v}).obj (dgNerve R C))
    ((SSet.uliftFunctor.{max (u + 1) v w,max u w}).obj (dgNerve R D))
  change KanComplex (pullback
    (pinchedHomMap (F2.arrowEndpointPair Z) (dgGluingLaxHomArrowVertex R C D M X)
      (dgGluingLaxHomArrowVertex R C D M Y)) (dgGluingLaxHomPinchedInputBase R C D M X Y))
  exact HomotopyLimits.pullback_kanComplex_of_fibration _ _
end SerrePositivity.InfinityCategories
