module

public import SerrePositivity.InfinityCategories.F1.FunctorCategories.FullyFaithfulFunctorIsoCoherence
public import SerrePositivity.InfinityCategories.F1.FunctorCategories.IsoTriangleIdentity
public import SerrePositivity.InfinityCategories.F2.FunctorIsoWhiskerAlgebra

/-!
概要：充満忠実な後合成で指定三角等式を元の三辺へ反映する。
方針：三端点と指定像を照合し、同じ合成の像の等式を充満忠実性で反映する。
規約：指定された元の三辺と端点表示を保持する。
使われ方：局所 over 自然性の三角等式。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories

/-- 同じ三端点と指定像の照合後、充満忠実な後合成は三角等式を反映する。 -/
lemma IsFullyFaithful.reflectFunctorIsoTriangle_of_heq
    {X Y H : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    {f : X ⟶ Y} (hf : IsFullyFaithful f)
    {a b t : H ⟶ X} (e : FunctorIso a b) (k : FunctorIso b t) (d : FunctorIso a t)
    {a' b' t' : H ⟶ Y} (E : FunctorIso a' b') (K : FunctorIso b' t')
    (D : FunctorIso a' t') (ha : a ≫ f = a') (hb : b ≫ f = b') (ht : t ≫ f = t')
    (he : HEq (e.postcomp f) E) (hk : HEq (k.postcomp f) K)
    (hd : HEq (d.postcomp f) D) (h : IsoTriangleCommutes E K D) :
    IsoTriangleCommutes e k d := by
  apply hf.postcomp_functorIso_injective (e ≪≫ k) d
  have hp := iso_pasting_heq_of_endpoint_eq (e.postcomp f) (k.postcomp f) E K
    (congrArg (fun m ↦ SSet.HomotopyCategory.mk (functorVertex m)) ha)
    (congrArg (fun m ↦ SSet.HomotopyCategory.mk (functorVertex m)) hb)
    (congrArg (fun m ↦ SSet.HomotopyCategory.mk (functorVertex m)) ht) he.symm hk.symm
  exact eq_of_heq ((heq_of_eq (F2.functorIso_postcomp_trans e k f)).trans
    (hp.trans ((heq_of_eq h).trans hd.symm)))

end SerrePositivity.InfinityCategories
