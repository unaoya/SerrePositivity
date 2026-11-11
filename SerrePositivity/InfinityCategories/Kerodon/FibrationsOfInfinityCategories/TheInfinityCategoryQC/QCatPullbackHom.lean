module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.CorePullbackIso
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.QCatPullbackCone
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks

/-!
概要：QCat の引き戻し錐の全豊穣 Hom の交換同型。
方針：元の単体集合の引き戻しと全ての試験対象の豊穣 Hom を比較する。
規約：小さい対象の宇宙は u、coherent nerve の宇宙は u+1。
使われ方：Cat_∞ の引き戻しの構成と普遍性。

対応節は Kerodon 5.5（Tag 01YV）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalClosed SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC

variable {E F B : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.QCat.{u}} (p : E ⟶ B) (q : F ⟶ B)
variable [InnerFibration (show E.obj ⟶ B.obj from p)]

/-- 概要：QCat の引き戻しの豊穣 Hom は豊穣 Hom の引き戻しと同型。
方針：内部 Hom の引き戻し保存に core を適用し、core の交換同型を合成する。
規約：第一の射の右持ち上げ条件により内部 Hom の inner 性を確保する。
使われ方：全試験対象からの実際の豊穣 Hom の極限性。 -/
def qCatPullbackHomIso (T : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.QCat.{u}) (hp : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.EquivalenceLifting (show E.obj ⟶ B.obj from p)) :
    SimplicialCategory.sHom T (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.qCatPullbackObject p q) ≅
      pullback (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreMap ((ihom T.obj).map (show E.obj ⟶ B.obj from p)))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreMap ((ihom T.obj).map (show F.obj ⟶ B.obj from q))) := by
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.EquivalenceLifting.innerFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.EquivalenceLifting.internalHom hp T.obj)
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreFunctor.mapIso (PreservesPullback.iso (ihom T.obj)
    (show E.obj ⟶ B.obj from p) (show F.obj ⟶ B.obj from q)) ≪≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.corePullbackIso ((ihom T.obj).map (show E.obj ⟶ B.obj from p))
        ((ihom T.obj).map (show F.obj ⟶ B.obj from q))
/-- 概要：豊穣 Hom の引き戻し同型は元の第一射影の後合成を保つ。
方針：内部 Hom と core の二つの交換同型の第一射影を計算する。
規約：順方向の標準比較射の厳密な等式。
使われ方：実際の錐の第一成分の照合。 -/
lemma qCatPullbackHomIso_fst (T : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.QCat.{u})
    (hp : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.EquivalenceLifting (show E.obj ⟶ B.obj from p)) :
    (qCatPullbackHomIso p q T hp).hom ≫
      pullback.fst (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreMap ((ihom T.obj).map (show E.obj ⟶ B.obj from p)))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreMap ((ihom T.obj).map (show F.obj ⟶ B.obj from q))) =
      ((SimplicialCategory.sHomFunctor _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.QCat.{u}).obj (Opposite.op T)).map
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.qCatPullbackOrdinaryCone p q).fst := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.qCatHom_postcomp]
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreFunctor.map (PreservesPullback.iso (ihom T.obj)
    (show E.obj ⟶ B.obj from p) (show F.obj ⟶ B.obj from q)).hom ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.corePullbackMap _ _ ≫ pullback.fst _ _ = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.corePullbackMap_fst]
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreFunctor.map (PreservesPullback.iso (ihom T.obj)
    (show E.obj ⟶ B.obj from p) (show F.obj ⟶ B.obj from q)).hom ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreFunctor.map (pullback.fst _ _) = _
  rw [← Functor.map_comp, PreservesPullback.iso_hom_fst]
  rfl
/-- 概要：豊穣 Hom の引き戻し同型は元の第二射影の後合成を保つ。
方針：内部 Hom と core の二つの交換同型の第二射影を計算する。
規約：順方向の標準比較射の厳密な等式。
使われ方：実際の錐の第二成分の照合。 -/
lemma qCatPullbackHomIso_snd (T : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.QCat.{u})
    (hp : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.EquivalenceLifting (show E.obj ⟶ B.obj from p)) :
    (qCatPullbackHomIso p q T hp).hom ≫
      pullback.snd (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreMap ((ihom T.obj).map (show E.obj ⟶ B.obj from p)))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreMap ((ihom T.obj).map (show F.obj ⟶ B.obj from q))) =
      ((SimplicialCategory.sHomFunctor _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.QCat.{u}).obj (Opposite.op T)).map
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.qCatPullbackOrdinaryCone p q).snd := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.qCatHom_postcomp]
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreFunctor.map (PreservesPullback.iso (ihom T.obj)
    (show E.obj ⟶ B.obj from p) (show F.obj ⟶ B.obj from q)).hom ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.corePullbackMap _ _ ≫ pullback.snd _ _ = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.corePullbackMap_snd]
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreFunctor.map (PreservesPullback.iso (ihom T.obj)
    (show E.obj ⟶ B.obj from p) (show F.obj ⟶ B.obj from q)).hom ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreFunctor.map (pullback.snd _ _) = _
  rw [← Functor.map_comp, PreservesPullback.iso_hom_snd]
  rfl
end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
