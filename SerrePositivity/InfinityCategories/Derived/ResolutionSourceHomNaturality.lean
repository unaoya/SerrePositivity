module
public import SerrePositivity.InfinityCategories.Derived.ResolutionCounitHomNaturality
public import SerrePositivity.InfinityCategories.Derived.ResolutionSourceComparisonNormalization
public import SerrePositivity.InfinityCategories.Derived.FunctorHomSquareTransport
public import SerrePositivity.InfinityCategories.Derived.FunctorHomFaithfulPostcomposition
public import SerrePositivity.InfinityCategories.Derived.FunctorHomIsIsoTransport
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
namespace SerrePositivity.InfinityCategories
open CategoryTheory SSet MonoidalClosed
lemma qCatResolutionSourceComparisonIso_hom_naturality
    {X Y A B : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    [Quasicategory A] [Quasicategory B]
    (Q : QCatEquivalence X A) (S : QCatEquivalence Y B)
    (h k : A ⟶ B) (H K : X ⟶ Y)
    (hs : H ≫ S.hom = Q.hom ≫ h) (ks : K ≫ S.hom = Q.hom ≫ k)
    (a : FunctorHom h k) (ε : FunctorHom H K)
    (he : HEq (functorHomPostcomp H K S.hom ε)
      (functorHomPrecomp h k Q.hom a)) :
    (qCatResolutionSourceComparisonIso Q S h H hs).hom ≫
        functorHomPostcomp h k S.inv a =
      functorHomPrecomp H K Q.inv ε ≫
        (qCatResolutionSourceComparisonIso Q S k K ks).hom := by
  let d := qCatResolutionSourceComparisonIso Q S h H hs
  let t := qCatResolutionSourceComparisonIso Q S k K ks
  let c := resolutionCounitComparison Q.invHomIso S.invHomIso h
  let b := resolutionCounitComparison Q.invHomIso S.invHomIso k
  have hf : (Q.inv ≫ H) ≫ S.hom = (Q.inv ≫ Q.hom) ≫ h := by
    rw [Category.assoc, hs, ← Category.assoc]
  have hg : (h ≫ S.inv) ≫ S.hom = h ≫ (S.inv ≫ S.hom) := Category.assoc _ _ _
  have hh : (Q.inv ≫ K) ≫ S.hom = (Q.inv ≫ Q.hom) ≫ k := by
    rw [Category.assoc, ks, ← Category.assoc]
  have hk : (k ≫ S.inv) ≫ S.hom = k ≫ (S.inv ≫ S.hom) := Category.assoc _ _ _
  have hd : HEq (functorHomPostcomp (Q.inv ≫ H) (h ≫ S.inv) S.hom d.hom) c.hom := by
    have hc := (heq_of_eq (qCatResolutionSourceComparisonIso_postcomp Q S h H hs)).trans
      (qCatResolutionBaseComparisonIso_heq Q S h H hs)
    exact (heq_of_eq (functorIso_postcomp_hom_typed d S.hom)).symm.trans
      (functorIso_hom_heq_of_endpoint_heq (d.postcomp S.hom) c hf hg hc)
  have ht : HEq (functorHomPostcomp (Q.inv ≫ K) (k ≫ S.inv) S.hom t.hom) b.hom := by
    have hc := (heq_of_eq (qCatResolutionSourceComparisonIso_postcomp Q S k K ks)).trans
      (qCatResolutionBaseComparisonIso_heq Q S k K ks)
    exact (heq_of_eq (functorIso_postcomp_hom_typed t S.hom)).symm.trans
      (functorIso_hom_heq_of_endpoint_heq (t.postcomp S.hom) b hh hk hc)
  have hr : HEq
      (functorHomPostcomp (h ≫ S.inv) (k ≫ S.inv) S.hom
        (functorHomPostcomp h k S.inv a))
      (functorHomPostcomp h k (S.inv ≫ S.hom) a) :=
    heq_of_eq (functorHomPostcomp_postcomp h k S.inv S.hom a)
  have hq : HEq
      (functorHomPostcomp (Q.inv ≫ H) (Q.inv ≫ K) S.hom
        (functorHomPrecomp H K Q.inv ε))
      (functorHomPrecomp h k (Q.inv ≫ Q.hom) a) := by
    have h₀ := heq_of_eq (functorHomPrecomp_postcomp H K Q.inv S.hom ε)
    have h₁' := functorHom_precomp_heq
      (functorHomPostcomp H K S.hom ε) (functorHomPrecomp h k Q.hom a)
      hs ks he Q.inv
    exact h₀.trans (h₁'.trans
      (heq_of_eq (functorHomPrecomp_precomp h k Q.hom Q.inv a)))
  have hp := functorHom_two_two_eq_of_heq
    (functorHomPostcomp (Q.inv ≫ H) (h ≫ S.inv) S.hom d.hom)
    (functorHomPostcomp (h ≫ S.inv) (k ≫ S.inv) S.hom
      (functorHomPostcomp h k S.inv a))
    (functorHomPostcomp (Q.inv ≫ H) (Q.inv ≫ K) S.hom
      (functorHomPrecomp H K Q.inv ε))
    (functorHomPostcomp (Q.inv ≫ K) (k ≫ S.inv) S.hom t.hom)
    c.hom (functorHomPostcomp h k (S.inv ≫ S.hom) a)
    (functorHomPrecomp h k (Q.inv ≫ Q.hom) a) b.hom
    hf hg hh hk hd hr hq ht
    (resolutionCounitComparison_hom_naturality Q.invHomIso S.invHomIso a)
  apply functorHom_postcomp_injective_of_isFullyFaithful S.isQCatEquivalence.isFullyFaithful
  simpa only [functorHomPostcomp, CategoryTheory.Functor.map_comp] using! hp
end SerrePositivity.InfinityCategories
