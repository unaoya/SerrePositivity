module
public import SerrePositivity.KST.SConstruction.CubicalSerreDayMonoidal

/-! # 強モノイダル Serre 鎖の元の比較射の回収
概要：全 cubical sets 上の構造射から、元の Day 比較と単位生成射を回収する。
方針：同じ同型の順逆を使う構造定義と、元の全 cell の評価式を適用する。
規約：元の鎖関手を置換しない。使われ方：cubical rigidification と余モノイドの比較。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory Opposite
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A]

/-- tensorator は元の両生成余極限から作った組み立て。 -/
lemma cubicalDaySerre_tensorator (X Y : CubicalDaySet.{u}) :
    Functor.LaxMonoidal.μ (cubicalDaySerreChains A) X Y =
      cubicalSerreDayInverse A X.functor Y.functor := rfl

/-- cotensorator は元の全 Day tensor の鎖比較。 -/
lemma cubicalDaySerre_cotensorator (X Y : CubicalDaySet.{u}) :
    Functor.OplaxMonoidal.δ (cubicalDaySerreChains A) X Y =
      cubicalSerreDayComparison A X.functor Y.functor := rfl

/-- 単位射は元の単位生成 cell の同じ鎖射。 -/
lemma cubicalDaySerre_unit :
    Functor.LaxMonoidal.ε (cubicalDaySerreChains A) =
      cubicalSerreCell A (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk 0) cubicalDayUnitCell := rfl

/-- 逆単位射は元の Day 単位上の同じ Serre 増大。 -/
lemma cubicalDaySerre_counit :
    Functor.OplaxMonoidal.η (cubicalDaySerreChains A) =
      cubicalSerreAugmentation A cubicalDayUnit :=
  cubicalSerreDayUnitIso_augmentation A

/-- 元の全ての両 cell 上で tensorator は同じ Serre 組み立てを回収する。 -/
lemma cubicalDaySerre_tensorator_cell {K L : CubicalSet.{u}}
    (c d : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube) (x : K.obj (op c)) (y : L.obj (op d)) :
    (cubicalSerreCell A c x ⊗ₘ cubicalSerreCell A d y) ≫
        Functor.LaxMonoidal.μ (cubicalDaySerreChains A) (DayFunctor.mk K) (DayFunctor.mk L) =
      cubicalSerreDayAssembly A c d x y :=
  cubicalSerreDayInverse_cell A c d x y

/-- 元の全連結 cell 上で cotensorator は同じ元の両鎖射の比較を回収する。 -/
lemma cubicalDaySerre_cotensorator_cell {K L : CubicalSet.{u}}
    (c d : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube) (x : K.obj (op c)) (y : L.obj (op d)) :
    cubicalSerreCell A (concreteCubeTensorObj c d) (cubicalDayTensorCell c d x y) ≫
        Functor.OplaxMonoidal.δ (cubicalDaySerreChains A) (DayFunctor.mk K) (DayFunctor.mk L) =
      cubicalSerreDayPair A c d x y :=
  cubicalSerreDayComparison_cell A c d x y

end SerrePositivity.KST.SConstruction
