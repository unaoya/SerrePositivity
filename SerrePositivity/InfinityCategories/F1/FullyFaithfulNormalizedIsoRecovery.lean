module

public import SerrePositivity.InfinityCategories.F1.FullyFaithfulFunctorIsoCoherence
public import SerrePositivity.InfinityCategories.F1.FunctorIsoPrecompositionProjection

/-!
概要：端点正規化した指定同型を充満忠実な後合成から厳密に回収する。
方針：逆像の像の等式と端点輸送の値の保持を組み合わせる。
規約：任意に選び直した同型ではなく元の指定値を保持する。
使われ方：局所自然性を元の全 Hom に戻した三角形の移送。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories

/-- 端点を正規化した同型の逆像は、後合成で元の指定値を回収する。 -/
lemma IsFullyFaithful.preimageNormalizedFunctorIso_postcomp_heq
    {X Y K : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    {f : X ⟶ Y} (hf : IsFullyFaithful f) (F G : K ⟶ X)
    {a b : K ⟶ Y} (e : FunctorIso a b) (ha : a = F ≫ f) (hb : b = G ≫ f) :
    HEq ((hf.preimageFunctorIso (F := F) (G := G)
      (F2.functorIsoOfEq e ha hb)).postcomp f) e := by
  exact (heq_of_eq (hf.preimageFunctorIso_postcomp
    (F2.functorIsoOfEq e ha hb))).trans (F2.functorIsoOfEq_heq e ha hb)

/-- 同じ逆像を元の作用で前合成しても、後合成で同じ指定値を回収する。 -/
lemma IsFullyFaithful.preimageNormalizedFunctorIso_precomp_postcomp_heq
    {X Y K H : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    {f : X ⟶ Y} (hf : IsFullyFaithful f) (F G : K ⟶ X)
    {a b : K ⟶ Y} (e : FunctorIso a b) (ha : a = F ≫ f) (hb : b = G ≫ f)
    (r : H ⟶ K) :
    HEq (((hf.preimageFunctorIso (F := F) (G := G)
      (F2.functorIsoOfEq e ha hb)).precomp r).postcomp f) (e.precomp r) := by
  have hp := hf.preimageFunctorIso_postcomp (F2.functorIsoOfEq e ha hb)
  have hh := congrArg (fun v ↦ FunctorIso.precomp v r) hp
  exact (heq_of_eq (F2.functorIso_precomp_postcomp _ r f)).trans
    ((heq_of_eq hh).trans (functorIsoOfEq_precomp_heq e ha hb r))

end SerrePositivity.InfinityCategories
