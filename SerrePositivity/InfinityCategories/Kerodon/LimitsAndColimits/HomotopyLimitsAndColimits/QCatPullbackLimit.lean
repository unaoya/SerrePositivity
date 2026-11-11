module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.QCatPullbackHom
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.StrictHomotopyLimits

/-!
概要：QCat の引き戻し錐の Cat_∞ 内の native な極限性。
方針：元の単体集合の引き戻しと全ての試験対象の豊穣 Hom を比較する。
規約：小さい対象の宇宙は u、coherent nerve の宇宙は u+1。
使われ方：Cat_∞ の引き戻しの構成と普遍性。

対応節は Kerodon 7.5（Tag 039Y）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalClosed SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits

variable {E F B : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.QCat.{u}} (p : E ⟶ B) (q : F ⟶ B)
variable [InnerFibration (show E.obj ⟶ B.obj from p)]

/-- 概要：QCat の引き戻し錐を各豊穣 Hom へ写すと厳密な極限錐となる。
方針：標準引き戻しの極限性を二射影を保つ豊穣 Hom の同型で移す。
規約：任意の小さい quasicategory T を試験対象に取る。
使われ方：coherent nerve の実際の極限判定の全 Hom 条件。 -/
def qCatPullbackHomCone_isLimit (T : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.QCat.{u})
    (hp : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.EquivalenceLifting (show E.obj ⟶ B.obj from p)) :
    IsLimit (((SimplicialCategory.sHomFunctor _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.QCat.{u}).obj (Opposite.op T)).mapCone
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.qCatPullbackOrdinaryCone p q)) := by
  apply (PullbackCone.isLimitMapConeEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.qCatPullbackOrdinaryCone p q)
    ((SimplicialCategory.sHomFunctor _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.QCat.{u}).obj (Opposite.op T))).symm.toFun
  have hr : IsPullback
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreMap ((ihom T.obj).map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.qCatPullbackOrdinaryCone p q).fst))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreMap ((ihom T.obj).map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.qCatPullbackOrdinaryCone p q).snd))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreMap ((ihom T.obj).map (show E.obj ⟶ B.obj from p)))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreMap ((ihom T.obj).map (show F.obj ⟶ B.obj from q))) := by
    refine (IsPullback.of_hasPullback _ _).of_iso
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.qCatPullbackHomIso p q T hp).symm (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_
      (by simp) (by simp)
    · simp only [Iso.refl_hom, Category.comp_id, Iso.symm_hom]
      have hf := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.qCatPullbackHomIso_fst p q T hp
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.qCatHom_postcomp] at hf
      rw [← hf, Iso.inv_hom_id_assoc]
    · simp only [Iso.refl_hom, Category.comp_id, Iso.symm_hom]
      have hs := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.qCatPullbackHomIso_snd p q T hp
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.qCatHom_postcomp] at hs
      rw [← hs, Iso.inv_hom_id_assoc]
  have hG : IsPullback
      (((SimplicialCategory.sHomFunctor _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.QCat.{u}).obj (Opposite.op T)).map
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.qCatPullbackOrdinaryCone p q).fst)
      (((SimplicialCategory.sHomFunctor _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.QCat.{u}).obj (Opposite.op T)).map
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.qCatPullbackOrdinaryCone p q).snd)
      (((SimplicialCategory.sHomFunctor _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.QCat.{u}).obj (Opposite.op T)).map p)
      (((SimplicialCategory.sHomFunctor _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.QCat.{u}).obj (Opposite.op T)).map q) := by
    simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.qCatHom_postcomp]
    exact hr
  exact hG.isLimit

/-- 概要：一脚が圏論的同値を持ち上げる QCat の引き戻し錐は Cat_∞ の極限錐。
方針：全豊穣 Hom の厳密な極限性と一脚の fibration 性を既存の判定に渡す。
規約：右脚に fibration 性を仮定しない。
使われ方：可逆 path 置換を使った Cat_∞ の実際の引き戻し。 -/
lemma qCatPullbackInfinityCone_isLimit
    (hp : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.EquivalenceLifting (show E.obj ⟶ B.obj from p)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentCone (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.qCatPullbackCone p q)) := by
  have : ∀ T : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.QCat.{u}, Fibration
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.qCatPullbackDiagram p q) T).map
        (AsSmall.up.map WalkingCospan.Hom.inl)) := fun T ↦ by
    change Fibration (((SimplicialCategory.sHomFunctor _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.QCat.{u}).obj (Opposite.op T)).map p)
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.qCatHom_postcomp]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.coreMap_fibration_of_kanEquivalenceLifting _
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.EquivalenceLifting.internalHom hp T.obj)
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.strictCoherentCone_isLimit_of_cospan_homLimit (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.qCatPullbackCone p q)
  intro T
  exact (qCatPullbackHomCone_isLimit p q T hp).whiskerEquivalence
    (AsSmall.equiv : WalkingCospan ≌ AsSmall.{u} WalkingCospan).symm
end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
