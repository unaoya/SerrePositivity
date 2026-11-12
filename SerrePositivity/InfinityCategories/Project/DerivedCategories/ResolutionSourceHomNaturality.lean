module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.ResolutionCounitHomNaturality
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.ResolutionSourceComparisonNormalization
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.FunctorHomSquareTransport
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.FunctorHomFaithfulPostcomposition
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.FunctorHomIsIsoTransport
/-!
概要：指定余単位と完全充満性による元の入力比較の、任意全関手射自然性。
方針：全関手空間の交換則から同じ指定比較の正方形を得て、忠実性で反映する。
規約：比較を選び直さず、射の可逆性を要求しない。使われ方：分解変更の自然性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory SSet MonoidalClosed
lemma qCatResolutionSourceComparisonIso_hom_naturality
    {X Y A B : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    [Quasicategory A] [Quasicategory B]
    (Q : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence X A) (S : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence Y B)
    (h k : A ⟶ B) (H K : X ⟶ Y)
    (hs : H ≫ S.hom = Q.hom ≫ h) (ks : K ≫ S.hom = Q.hom ≫ k)
    (a : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom h k) (ε : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom H K)
    (he : HEq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPostcomp H K S.hom ε)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPrecomp h k Q.hom a)) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.qCatResolutionSourceComparisonIso Q S h H hs).hom ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPostcomp h k S.inv a =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPrecomp H K Q.inv ε ≫
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.qCatResolutionSourceComparisonIso Q S k K ks).hom := by
  let d := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.qCatResolutionSourceComparisonIso Q S h H hs
  let t := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.qCatResolutionSourceComparisonIso Q S k K ks
  let c := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolutionCounitComparison Q.invHomIso S.invHomIso h
  let b := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolutionCounitComparison Q.invHomIso S.invHomIso k
  have hf : (Q.inv ≫ H) ≫ S.hom = (Q.inv ≫ Q.hom) ≫ h := by
    rw [Category.assoc, hs, ← Category.assoc]
  have hg : (h ≫ S.inv) ≫ S.hom = h ≫ (S.inv ≫ S.hom) := Category.assoc _ _ _
  have hh : (Q.inv ≫ K) ≫ S.hom = (Q.inv ≫ Q.hom) ≫ k := by
    rw [Category.assoc, ks, ← Category.assoc]
  have hk : (k ≫ S.inv) ≫ S.hom = k ≫ (S.inv ≫ S.hom) := Category.assoc _ _ _
  have hd : HEq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPostcomp (Q.inv ≫ H) (h ≫ S.inv) S.hom d.hom) c.hom := by
    have hc := (heq_of_eq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.qCatResolutionSourceComparisonIso_postcomp Q S h H hs)).trans
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.qCatResolutionBaseComparisonIso_heq Q S h H hs)
    exact (heq_of_eq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorIso_postcomp_hom_typed d S.hom)).symm.trans
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorIso_hom_heq_of_endpoint_heq (d.postcomp S.hom) c hf hg hc)
  have ht : HEq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPostcomp (Q.inv ≫ K) (k ≫ S.inv) S.hom t.hom) b.hom := by
    have hc := (heq_of_eq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.qCatResolutionSourceComparisonIso_postcomp Q S k K ks)).trans
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.qCatResolutionBaseComparisonIso_heq Q S k K ks)
    exact (heq_of_eq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorIso_postcomp_hom_typed t S.hom)).symm.trans
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorIso_hom_heq_of_endpoint_heq (t.postcomp S.hom) b hh hk hc)
  have hr : HEq
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPostcomp (h ≫ S.inv) (k ≫ S.inv) S.hom
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPostcomp h k S.inv a))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPostcomp h k (S.inv ≫ S.hom) a) :=
    heq_of_eq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPostcomp_postcomp h k S.inv S.hom a)
  have hq : HEq
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPostcomp (Q.inv ≫ H) (Q.inv ≫ K) S.hom
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPrecomp H K Q.inv ε))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPrecomp h k (Q.inv ≫ Q.hom) a) := by
    have h₀ := heq_of_eq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPrecomp_postcomp H K Q.inv S.hom ε)
    have h₁' := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHom_precomp_heq
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPostcomp H K S.hom ε) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPrecomp h k Q.hom a)
      hs ks he Q.inv
    exact h₀.trans (h₁'.trans
      (heq_of_eq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPrecomp_precomp h k Q.hom Q.inv a)))
  have hp := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHom_two_two_eq_of_heq
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPostcomp (Q.inv ≫ H) (h ≫ S.inv) S.hom d.hom)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPostcomp (h ≫ S.inv) (k ≫ S.inv) S.hom
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPostcomp h k S.inv a))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPostcomp (Q.inv ≫ H) (Q.inv ≫ K) S.hom
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPrecomp H K Q.inv ε))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPostcomp (Q.inv ≫ K) (k ≫ S.inv) S.hom t.hom)
    c.hom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPostcomp h k (S.inv ≫ S.hom) a)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPrecomp h k (Q.inv ≫ Q.hom) a) b.hom
    hf hg hh hk hd hr hq ht
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolutionCounitComparison_hom_naturality Q.invHomIso S.invHomIso a)
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHom_postcomp_injective_of_isFullyFaithful S.isQCatEquivalence.isFullyFaithful
  simpa only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPostcomp, CategoryTheory.Functor.map_comp] using! hp
end SerrePositivity.InfinityCategories.Project.DerivedCategories
