module

public import SerrePositivity.InfinityCategories.F1.FunctorCategories.PathCorrectedSquarePrecompositionCoherence
public import SerrePositivity.InfinityCategories.F1.FunctorCategories.IsoTriangleIdentity

/-!
概要：元の補正成分と大域自然性の指定合成は、共有頂点で直接自然性を回収する。
方針：前合成した補正 path の指定像を、元の自然性の三角等式へ貼り合わせる。
規約：補正 path と元の三辺を選び直さない。
使われ方：元の分類 Hom 作用と補正 pullback 比較の同定。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories

/-- 補正成分と元の大域自然性の合成は、共有頂点で同じ直接自然性を回収する。 -/
lemma PathCorrectedFunctorSquare.globalComposite_postcomp_heq
    {H A X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    {q : X ⟶ Y} {f : A ⟶ X} {g : A ⟶ Y} {e : FunctorIso g (f ≫ q)}
    (s : PathCorrectedFunctorSquare q f g e) (r : H ⟶ A)
    {t : H ⟶ X} (n : FunctorIso (r ≫ f) t)
    {a' b' t' : H ⟶ Y} (E : FunctorIso a' b') (K : FunctorIso b' t')
    (D : FunctorIso a' t') (ha : (r ≫ s.map) ≫ q = a')
    (hb : (r ≫ f) ≫ q = b') (ht : t ≫ q = t')
    (he : HEq (e.precomp r) E) (hk : HEq (n.postcomp q) K)
    (h : IsoTriangleCommutes E K D) :
    HEq (FunctorIso.postcomp (s.exactComponentIso.precomp r ≪≫ n) q) D := by
  have hc := (s.exactComponentIso_precomp_postcomp_heq r).trans he
  have hp := iso_pasting_heq_of_endpoint_eq
    ((s.exactComponentIso.precomp r).postcomp q) (n.postcomp q) E K
    (congrArg (fun m ↦ SSet.HomotopyCategory.mk (functorVertex m)) ha)
    (congrArg (fun m ↦ SSet.HomotopyCategory.mk (functorVertex m)) hb)
    (congrArg (fun m ↦ SSet.HomotopyCategory.mk (functorVertex m)) ht) hc.symm hk.symm
  exact (heq_of_eq (F2.functorIso_postcomp_trans (s.exactComponentIso.precomp r) n q)).trans
    (hp.trans (heq_of_eq h))

end SerrePositivity.InfinityCategories
