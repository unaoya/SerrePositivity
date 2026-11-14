module
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.VertexTransport.FunctorIsoTransportAlgebra
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.FunctorIsoTransportAlgebra
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Homotopies.Resolutions.ResolutionSourceComparisonNormalization
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.FunctorComparisons.SimplicialFunctors.FunctorIsoFaithfulTransport
/-!
概要：三つの指定入力分解に対し、回収した同じ比較は前合成の合成則を満たす。
方針：標的入力射影への忠実な後合成で、指定余単位比較の cocycle 則へ戻す。
規約：三端点の等式を明示する。使われ方：元の出力分解比較と kernel 合成子の照合。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory SSet
variable {X Y Z A B C : SSet.{u}} [Quasicategory X] [Quasicategory Y] [Quasicategory Z]
  [Quasicategory A] [Quasicategory B] [Quasicategory C]
/-- 二段の指定入力比較は、同じ合成入力写像の指定比較に厳密に一致する。 -/
lemma qCatResolutionSourceComparisonIso_comp (Q : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence X A) (S : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence Y B)
    (T : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence Z C) (h : A ⟶ B) (k : B ⟶ C) (H : X ⟶ Y) (J : Y ⟶ Z)
    (hs : H ≫ S.hom = Q.hom ≫ h) (ht : J ≫ T.hom = S.hom ≫ k)
    (hu : (H ≫ J) ≫ T.hom = Q.hom ≫ (h ≫ k)) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.qCatResolutionSourceComparisonIso Q T (h ≫ k) (H ≫ J) hu =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.qCatResolutionSourceComparisonIso Q S h H hs).postcomp J ≪≫
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.qCatResolutionSourceComparisonIso S T k J ht).precomp h := by
  let d := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.qCatResolutionSourceComparisonIso Q S h H hs
  let c := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.qCatResolutionSourceComparisonIso S T k J ht
  let b := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.qCatResolutionBaseComparisonIso Q S h H hs
  let a := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.qCatResolutionBaseComparisonIso S T k J ht
  let n := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolutionCounitComparison Q.invHomIso S.invHomIso h
  let m := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolutionCounitComparison S.invHomIso T.invHomIso k
  have ha : HEq ((d.postcomp J).postcomp T.hom) (n.postcomp k) := by
    have h1 := heq_of_eq (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_postcomp_postcomp d J T.hom)
    have h2 : HEq (d.postcomp (J ≫ T.hom)) (d.postcomp (S.hom ≫ k)) :=
      _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_postcomp_heq_of_map_eq d ht.symm
    have h3 := heq_of_eq (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_postcomp_postcomp d S.hom k).symm
    have h4 := heq_of_eq (congrArg
      (fun e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso ((Q.inv ≫ H) ≫ S.hom) ((h ≫ S.inv) ≫ S.hom) => e.postcomp k)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.qCatResolutionSourceComparisonIso_postcomp Q S h H hs))
    have h5 := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_postcomp_heq_of_heq n b
      ((congrArg (fun t => Q.inv ≫ t) hs).symm) rfl
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.qCatResolutionBaseComparisonIso_heq Q S h H hs) k
    exact h1.trans (h2.trans (h3.trans (h4.trans h5)))
  have hb : HEq ((c.precomp h).postcomp T.hom) (m.precomp h) := by
    have h1 := heq_of_eq (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_precomp_postcomp c h T.hom)
    have h2 := heq_of_eq (congrArg
      (fun e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso ((S.inv ≫ J) ≫ T.hom) ((k ≫ T.inv) ≫ T.hom) => e.precomp h)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.qCatResolutionSourceComparisonIso_postcomp S T k J ht))
    have h3 := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.functorIso_precomp_heq_of_heq m a
      ((congrArg (fun t => S.inv ≫ t) ht).symm) rfl
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.qCatResolutionBaseComparisonIso_heq S T k J ht) h
    exact h1.trans (h2.trans h3)
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorIso_postcomp_injective_of_isFullyFaithful T.isQCatEquivalence.isFullyFaithful
  dsimp only
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.qCatResolutionSourceComparisonIso_postcomp, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_postcomp_trans]
  apply eq_of_heq
  have hc := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorIso_trans_heq ((d.postcomp J).postcomp T.hom)
    ((c.precomp h).postcomp T.hom) (n.postcomp k) (m.precomp h)
    (congrArg (fun t => Q.inv ≫ t) hu)
    (congrArg (fun t => h ≫ S.inv ≫ t) ht) rfl ha hb
  exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.qCatResolutionBaseComparisonIso_heq Q T (h ≫ k) (H ≫ J) hu).trans
    ((heq_of_eq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolutionCounitComparison_comp Q.invHomIso S.invHomIso T.invHomIso h k)).trans
      hc.symm)
end SerrePositivity.InfinityCategories.Project.DerivedCategories
