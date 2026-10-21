module

public import SerrePositivity.InfinityCategories.F1.FullyFaithfulFunctorIsoCoherence
public import SerrePositivity.InfinityCategories.F1.FunctorIsoPrecompositionProjection
public import SerrePositivity.InfinityCategories.F1.FunctorIsoSquareIdentity

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

/-- 元の作用で前合成した逆像の像は、正規化前の両端の射も回収する。 -/
lemma IsFullyFaithful.preimageNormalizedFunctorIso_precomp_postcomp_endpoints
    {X Y K H : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    {f : X ⟶ Y} (hf : IsFullyFaithful f) (F G : K ⟶ X)
    {a b : K ⟶ Y} (e : FunctorIso a b) (ha : a = F ≫ f) (hb : b = G ≫ f)
    (r : H ⟶ K) :
    (((hf.preimageFunctorIso (F := F) (G := G)
      (F2.functorIsoOfEq e ha hb)).precomp r).postcomp f).sourceMap = r ≫ a ∧
    (((hf.preimageFunctorIso (F := F) (G := G)
      (F2.functorIsoOfEq e ha hb)).precomp r).postcomp f).targetMap = r ≫ b := by
  constructor
  · exact (Category.assoc r F f).trans (congrArg (fun m ↦ r ≫ m) ha.symm)
  · exact (Category.assoc r G f).trans (congrArg (fun m ↦ r ≫ m) hb.symm)

/-- 後合成の始点は、元の始点の同じ後合成。 -/
lemma FunctorIso.sourceMap_postcomp {K X Y : SSet.{u}} {F G : K ⟶ X}
    (e : FunctorIso F G) (f : X ⟶ Y) :
    (e.postcomp f).sourceMap = e.sourceMap ≫ f := rfl

/-- 後合成の終点は、元の終点の同じ後合成。 -/
lemma FunctorIso.targetMap_postcomp {K X Y : SSet.{u}} {F G : K ⟶ X}
    (e : FunctorIso F G) (f : X ⟶ Y) :
    (e.postcomp f).targetMap = e.targetMap ≫ f := rfl

end SerrePositivity.InfinityCategories
