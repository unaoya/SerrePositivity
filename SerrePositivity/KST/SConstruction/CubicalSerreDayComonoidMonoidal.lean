module
public import SerrePositivity.KST.SConstruction.ComonoidMonoidalLift
public import SerrePositivity.KST.SConstruction.CubicalSerreDayComonoidComparison
public import SerrePositivity.KST.SConstruction.CubicalSerreDayComonoidUnit
public import SerrePositivity.KST.SConstruction.CubicalSerreDayMonoidalRecovery

/-! # 全 cubical sets の Serre 余モノイド値の強モノイダル関手
概要：既存の対角・増大を保つ Day 比較と単位比較を強モノイダル関手へ束ねる。
方針：元の鎖関手の自然性・結合・左右単位法則を忠実な忘却関手で反映する。
規約：元の余モノイド構造と全構造射を保持。使われ方：Λ の oplax tensor への接続。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A]

/-- 元の全 Serre 余モノイドを Day モノイダル圏上で読む。 -/
def cubicalDaySerreComonoids : CubicalDaySet.{u} ⥤ Comon (Complex A) :=
  cubicalDayEquivalence.functor ⋙ cubicalSerreComonoidFunctor A

/-- 元の Day 余モノイド比較と単位比較による強モノイダルデータ。 -/
def cubicalDaySerreComonoidsCoreMonoidal : (cubicalDaySerreComonoids A).CoreMonoidal :=
  comonoidCoreMonoidalLift (cubicalDaySerreComonoids A)
    (cubicalSerreDayComonoidUnit A)
    (fun X Y => (cubicalSerreDayComonoidIso A X.functor Y.functor).symm)
    (fun f X' => (cubicalDaySerreCoreMonoidal A).μIso_hom_natural_left f X')
    (fun X' f => (cubicalDaySerreCoreMonoidal A).μIso_hom_natural_right X' f)
    (fun X Y Z => (cubicalDaySerreCoreMonoidal A).associativity X Y Z)
    (fun X => cubicalSerreDayInverse_leftUnit A X.functor)
    (fun X => cubicalSerreDayInverse_rightUnit A X.functor)

/-- 元の Serre 余モノイド値関手は全 cubical sets の Day tensor を強モノイダルに保つ。 -/
instance cubicalDaySerreComonoidsMonoidal : (cubicalDaySerreComonoids A).Monoidal :=
  (cubicalDaySerreComonoidsCoreMonoidal A).toMonoidal

end SerrePositivity.KST.SConstruction
