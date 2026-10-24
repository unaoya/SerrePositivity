module

public import SerrePositivity.InfinityCategories.F2.CatInfinity.QCatPullbackHom
public import SerrePositivity.InfinityCategories.HomotopyLimits.StrictHomotopyLimits

/-!
概要：QCat の引き戻し錐の Cat_∞ 内の native な極限性。
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

/-- 概要：QCat の引き戻し錐を各豊穣 Hom へ写すと厳密な極限錐となる。
方針：標準引き戻しの極限性を二射影を保つ豊穣 Hom の同型で移す。
規約：任意の小さい quasicategory T を試験対象に取る。
使われ方：coherent nerve の実際の極限判定の全 Hom 条件。 -/
def qCatPullbackHomCone_isLimit (T : QCat.{u})
    (hp : SerrePositivity.InfinityCategories.F1B.EquivalenceLifting (show E.obj ⟶ B.obj from p)) :
    IsLimit (((SimplicialCategory.sHomFunctor QCat.{u}).obj (Opposite.op T)).mapCone
      (qCatPullbackOrdinaryCone p q)) := by
  apply (PullbackCone.isLimitMapConeEquiv (qCatPullbackOrdinaryCone p q)
    ((SimplicialCategory.sHomFunctor QCat.{u}).obj (Opposite.op T))).symm.toFun
  have hr : IsPullback
      (quasicategoryCoreMap ((ihom T.obj).map (qCatPullbackOrdinaryCone p q).fst))
      (quasicategoryCoreMap ((ihom T.obj).map (qCatPullbackOrdinaryCone p q).snd))
      (quasicategoryCoreMap ((ihom T.obj).map (show E.obj ⟶ B.obj from p)))
      (quasicategoryCoreMap ((ihom T.obj).map (show F.obj ⟶ B.obj from q))) := by
    refine (IsPullback.of_hasPullback _ _).of_iso
      (qCatPullbackHomIso p q T hp).symm (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_
      (by simp) (by simp)
    · simp only [Iso.refl_hom, Category.comp_id, Iso.symm_hom]
      have hf := qCatPullbackHomIso_fst p q T hp
      rw [qCatHom_postcomp] at hf
      rw [← hf, Iso.inv_hom_id_assoc]
    · simp only [Iso.refl_hom, Category.comp_id, Iso.symm_hom]
      have hs := qCatPullbackHomIso_snd p q T hp
      rw [qCatHom_postcomp] at hs
      rw [← hs, Iso.inv_hom_id_assoc]
  have hG : IsPullback
      (((SimplicialCategory.sHomFunctor QCat.{u}).obj (Opposite.op T)).map
        (qCatPullbackOrdinaryCone p q).fst)
      (((SimplicialCategory.sHomFunctor QCat.{u}).obj (Opposite.op T)).map
        (qCatPullbackOrdinaryCone p q).snd)
      (((SimplicialCategory.sHomFunctor QCat.{u}).obj (Opposite.op T)).map p)
      (((SimplicialCategory.sHomFunctor QCat.{u}).obj (Opposite.op T)).map q) := by
    simp only [qCatHom_postcomp]
    exact hr
  exact hG.isLimit

/-- 概要：一脚が圏論的同値を持ち上げる QCat の引き戻し錐は Cat_∞ の極限錐。
方針：全豊穣 Hom の厳密な極限性と一脚の fibration 性を既存の判定に渡す。
規約：右脚に fibration 性を仮定しない。
使われ方：可逆 path 置換を使った Cat_∞ の実際の引き戻し。 -/
lemma qCatPullbackInfinityCone_isLimit
    (hp : SerrePositivity.InfinityCategories.F1B.EquivalenceLifting (show E.obj ⟶ B.obj from p)) :
    IsLimitCone (HomotopyLimits.strictCoherentCone (qCatPullbackCone p q)) := by
  have : ∀ T : QCat.{u}, Fibration
      ((HomotopyLimits.simplicialHomDiagram (qCatPullbackDiagram p q) T).map
        (AsSmall.up.map WalkingCospan.Hom.inl)) := fun T ↦ by
    change Fibration (((SimplicialCategory.sHomFunctor QCat.{u}).obj (Opposite.op T)).map p)
    rw [qCatHom_postcomp]
    exact coreMap_fibration_of_kanEquivalenceLifting _
      (SerrePositivity.InfinityCategories.F1B.EquivalenceLifting.internalHom hp T.obj)
  apply HomotopyLimits.strictCoherentCone_isLimit_of_cospan_homLimit (qCatPullbackCone p q)
  intro T
  exact (qCatPullbackHomCone_isLimit p q T hp).whiskerEquivalence
    (AsSmall.equiv : WalkingCospan ≌ AsSmall.{u} WalkingCospan).symm
end SerrePositivity.InfinityCategories.F2
