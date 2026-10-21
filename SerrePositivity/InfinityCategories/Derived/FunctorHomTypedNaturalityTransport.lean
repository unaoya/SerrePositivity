module
public import SerrePositivity.InfinityCategories.Derived.FunctorHomTypedWhiskerAlgebra
public import SerrePositivity.InfinityCategories.Derived.FunctorIsoPrecompositionReflection
/-!
概要：同じ比較四角形を型付き前後合成へ送り、全前合成から等式を反映する。
方針：実 h Fun の関手性と完全充満な前合成の単射性を使う。
規約：可逆性は追加しない。使われ方：元の κ の全射自然性。
-/
@[expose] public section
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory SSet MonoidalClosed
noncomputable section
lemma functorHomPostcomp_iso_square {X Y Z : SSet.{u}} {f f' g g' : X ⟶ Y}
    (c : FunctorIso f g) (c' : FunctorIso f' g') (q : FunctorHom f f')
    (r : FunctorHom g g') (H : Y ⟶ Z) (hs : c.hom ≫ r = q ≫ c'.hom) :
    (c.postcomp H).hom ≫ functorHomPostcomp g g' H r =
      functorHomPostcomp f f' H q ≫ (c'.postcomp H).hom := by
  have h := congrArg (fun z => functorHomPostcomp f g' H z) hs
  simpa only [functorHomPostcomp_comp, functorIso_postcomp_hom_typed] using! h
lemma functorHomPrecomp_iso_square {X A Y : SSet.{u}} {f f' g g' : A ⟶ Y}
    (c : FunctorIso f g) (c' : FunctorIso f' g') (q : FunctorHom f f')
    (r : FunctorHom g g') (L : X ⟶ A)
    (hs : (c.precomp L).hom ≫ functorHomPrecomp g g' L r =
      functorHomPrecomp f f' L q ≫ (c'.precomp L).hom) :
    functorHomPrecomp f g' L (c.hom ≫ r) =
      functorHomPrecomp f g' L (q ≫ c'.hom) := by
  simpa only [functorHomPrecomp_comp, functorIso_precomp_hom_typed] using! hs
lemma functorHomPrecomp_eq_of_isFullyFaithful {X A Y : SSet.{u}} [Quasicategory Y]
    (L : X ⟶ A) (hL : IsFullyFaithful ((pre L).app Y))
    {f g : A ⟶ Y} (a b : FunctorHom f g)
    (h : functorHomPrecomp f g L a = functorHomPrecomp f g L b) : a = b := by
  apply hL.toHoFullyFaithful.map_injective
  simpa only [functorHomPrecomp] using! h
end
end SerrePositivity.InfinityCategories
