module
public import SerrePositivity.InfinityCategories.Derived.FunctorHomTypedNaturalityTransport
/-!
概要：元の kernel 合成子の右変数自然性を、同じ通常比較と raw 経路で照合する。
方針：元の指定比較と射の値を保持し、全関手圏の実作用と可換四角形を使う。
規約：後続 kernel の平坦性・射の可逆性は要求しない。使われ方：模型変更の整合性。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory SSet
lemma functorHomPrecomp_iso_square_forward {X A Y : SSet.{u}}
    {f f' g g' : A ⟶ Y} (c : FunctorIso f g) (c' : FunctorIso f' g')
    (q : FunctorHom f f') (r : FunctorHom g g') (L : X ⟶ A)
    (hs : c.hom ≫ r = q ≫ c'.hom) :
    (c.precomp L).hom ≫ functorHomPrecomp g g' L r =
      functorHomPrecomp f f' L q ≫ (c'.precomp L).hom := by
  have h := congrArg (fun z => functorHomPrecomp f g' L z) hs
  simpa only [functorHomPrecomp_comp, functorIso_precomp_hom_typed] using! h
end SerrePositivity.InfinityCategories
