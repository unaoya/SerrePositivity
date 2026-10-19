module

public import SerrePositivity.InfinityCategories.F2.QCatPullbackCone
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks

/-!
概要：QCat の引き戻し錐の全豊穣 Hom の交換同型。
方針：元の単体集合の引き戻しと全ての試験対象の豊穣 Hom を比較する。
規約：小さい対象の宇宙は u、coherent nerve の宇宙は u+1。
使われ方：Cat_∞ の引き戻しの構成と普遍性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalClosed SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
namespace SerrePositivity.InfinityCategories.F2

variable {E F B : QCat.{u}} (p : E ⟶ B) (q : F ⟶ B)
variable [InnerFibration (show E.obj ⟶ B.obj from p)]

/-- 概要：QCat の引き戻しの豊穣 Hom は豊穣 Hom の引き戻しと同型。
方針：内部 Hom の引き戻し保存に core を適用し、core の交換同型を合成する。
規約：第一の射の右持ち上げ条件により内部 Hom の inner 性を確保する。
使われ方：全試験対象からの実際の豊穣 Hom の極限性。 -/
def qCatPullbackHomIso (T : QCat.{u}) (hp : F1B.KanEquivalenceLifting (show E.obj ⟶ B.obj from p)) :
    SimplicialCategory.sHom T (qCatPullbackObject p q) ≅
      pullback (quasicategoryCoreMap ((ihom T.obj).map (show E.obj ⟶ B.obj from p)))
        (quasicategoryCoreMap ((ihom T.obj).map (show F.obj ⟶ B.obj from q))) := by
  have := F1B.KanEquivalenceLifting.innerFibration (F1B.KanEquivalenceLifting.internalHom hp T.obj)
  exact quasicategoryCoreFunctor.mapIso (PreservesPullback.iso (ihom T.obj)
    (show E.obj ⟶ B.obj from p) (show F.obj ⟶ B.obj from q)) ≪≫
      corePullbackIso ((ihom T.obj).map (show E.obj ⟶ B.obj from p))
        ((ihom T.obj).map (show F.obj ⟶ B.obj from q))
/-- 概要：豊穣 Hom の引き戻し同型は元の第一射影の後合成を保つ。
方針：内部 Hom と core の二つの交換同型の第一射影を計算する。
規約：順方向の標準比較射の厳密な等式。
使われ方：実際の錐の第一成分の照合。 -/
lemma qCatPullbackHomIso_fst (T : QCat.{u})
    (hp : F1B.KanEquivalenceLifting (show E.obj ⟶ B.obj from p)) :
    (qCatPullbackHomIso p q T hp).hom ≫
      pullback.fst (quasicategoryCoreMap ((ihom T.obj).map (show E.obj ⟶ B.obj from p)))
        (quasicategoryCoreMap ((ihom T.obj).map (show F.obj ⟶ B.obj from q))) =
      ((SimplicialCategory.sHomFunctor QCat.{u}).obj (Opposite.op T)).map
        (qCatPullbackOrdinaryCone p q).fst := by
  rw [qCatHom_postcomp]
  change quasicategoryCoreFunctor.map (PreservesPullback.iso (ihom T.obj)
    (show E.obj ⟶ B.obj from p) (show F.obj ⟶ B.obj from q)).hom ≫
      corePullbackMap _ _ ≫ pullback.fst _ _ = _
  rw [corePullbackMap_fst]
  change quasicategoryCoreFunctor.map (PreservesPullback.iso (ihom T.obj)
    (show E.obj ⟶ B.obj from p) (show F.obj ⟶ B.obj from q)).hom ≫
      quasicategoryCoreFunctor.map (pullback.fst _ _) = _
  rw [← Functor.map_comp, PreservesPullback.iso_hom_fst]
  rfl
/-- 概要：豊穣 Hom の引き戻し同型は元の第二射影の後合成を保つ。
方針：内部 Hom と core の二つの交換同型の第二射影を計算する。
規約：順方向の標準比較射の厳密な等式。
使われ方：実際の錐の第二成分の照合。 -/
lemma qCatPullbackHomIso_snd (T : QCat.{u})
    (hp : F1B.KanEquivalenceLifting (show E.obj ⟶ B.obj from p)) :
    (qCatPullbackHomIso p q T hp).hom ≫
      pullback.snd (quasicategoryCoreMap ((ihom T.obj).map (show E.obj ⟶ B.obj from p)))
        (quasicategoryCoreMap ((ihom T.obj).map (show F.obj ⟶ B.obj from q))) =
      ((SimplicialCategory.sHomFunctor QCat.{u}).obj (Opposite.op T)).map
        (qCatPullbackOrdinaryCone p q).snd := by
  rw [qCatHom_postcomp]
  change quasicategoryCoreFunctor.map (PreservesPullback.iso (ihom T.obj)
    (show E.obj ⟶ B.obj from p) (show F.obj ⟶ B.obj from q)).hom ≫
      corePullbackMap _ _ ≫ pullback.snd _ _ = _
  rw [corePullbackMap_snd]
  change quasicategoryCoreFunctor.map (PreservesPullback.iso (ihom T.obj)
    (show E.obj ⟶ B.obj from p) (show F.obj ⟶ B.obj from q)).hom ≫
      quasicategoryCoreFunctor.map (pullback.snd _ _) = _
  rw [← Functor.map_comp, PreservesPullback.iso_hom_snd]
  rfl
end SerrePositivity.InfinityCategories.F2
