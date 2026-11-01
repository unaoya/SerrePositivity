module
public import SerrePositivity.InfinityCategories.Derived.FunctorHomSquareTransport
public import SerrePositivity.InfinityCategories.Core.FunctorIsoWhiskerHom
/-!
概要：元の指定同型の包含後の異種等式を、同じ前後合成射の異種等式へ移す。
方針：一般の全関手圏で同じ射の等式を証明し、指定値を保つ。
規約：可逆性は追加しない。使われ方：元の ξ と K-flat 合成比較の自然性。
-/
@[expose] public section
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory SSet MonoidalClosed
noncomputable section
lemma functorIso_lifted_hom_heq {A B X Y : SSet.{u}}
    {f g : A ⟶ X} {f' g' : B ⟶ Y}
    (c : FunctorIso f g) (c' : FunctorIso f' g') (i : A ⟶ B) (j : X ⟶ Y)
    (hf : f ≫ j = i ≫ f') (hg : g ≫ j = i ≫ g')
    (he : HEq (c.postcomp j) (c'.precomp i)) :
    HEq ((SSet.mapHomotopyCategory ((ihom A).map j)).map c.hom)
      ((SSet.mapHomotopyCategory ((pre i).app Y)).map c'.hom) := by
  have h := functorIso_hom_heq_of_endpoint_heq (c.postcomp j) (c'.precomp i) hf hg he
  simpa only [F2.functorIso_postcomp_hom, F2.functorIso_precomp_hom] using! h
end
end SerrePositivity.InfinityCategories
