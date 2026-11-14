module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Homotopies.Resolutions.ResolutionOutputPrecomposition
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.FullyFaithfulIsoRecovery
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.VertexTransport.FunctorIsoTransport
/-!
概要：二つの指定入力分解の前合成比較を、元の同じ基底比較とその忠実な回収へ分離する。
方針：二つの指定余単位の合成を先に固定し、標的入力分解の完全充満性で回収する。
規約：元の指定同型を保持する。使われ方：出力分解の前合成則と合成子の照合。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory SSet
variable {X Y A B : SSet.{u}} [Quasicategory X] [Quasicategory Y]
  [Quasicategory A] [Quasicategory B]
/-- 同じ二つの指定余単位による、元の基底上の入力比較。 -/
def qCatResolutionBaseComparisonIso (Q : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence X A) (S : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence Y B)
    (h : A ⟶ B) (H : X ⟶ Y) (hs : H ≫ S.hom = Q.hom ≫ h) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso ((Q.inv ≫ H) ≫ S.hom) ((h ≫ S.inv) ≫ S.hom) := by
  rw [Category.assoc, hs]
  have e1 := Q.invHomIso.postcomp h
  have e2 := S.invHomIso.precomp h
  simpa only [Category.assoc, Category.id_comp, Category.comp_id] using! e1 ≪≫ e2.symm
/-- 元の基底比較を、指定した同じ入力分解の完全充満性で回収する。 -/
def qCatResolutionSourceComparisonIso (Q : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence X A) (S : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence Y B)
    (h : A ⟶ B) (H : X ⟶ Y) (hs : H ≫ S.hom = Q.hom ≫ h) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (Q.inv ≫ H) (h ≫ S.inv) :=
  S.isQCatEquivalence.isFullyFaithful.preimageFunctorIso
    (qCatResolutionBaseComparisonIso Q S h H hs)
/-- 回収した入力比較は、標的入力射影を後合成すると元の指定基底比較へ厳密に戻る。 -/
lemma qCatResolutionSourceComparisonIso_postcomp
    (Q : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence X A) (S : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence Y B)
    (h : A ⟶ B) (H : X ⟶ Y) (hs : H ≫ S.hom = Q.hom ≫ h) :
    (qCatResolutionSourceComparisonIso Q S h H hs).postcomp S.hom =
      qCatResolutionBaseComparisonIso Q S h H hs :=
  S.isQCatEquivalence.isFullyFaithful.preimageFunctorIso_postcomp _
end SerrePositivity.InfinityCategories.Project.DerivedCategories
