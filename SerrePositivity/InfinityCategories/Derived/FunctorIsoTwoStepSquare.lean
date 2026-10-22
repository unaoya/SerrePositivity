module
public import SerrePositivity.InfinityCategories.Derived.FunctorHomTypedWhiskerAlgebra
/-!
概要：同じ二段の比較の可換四角形から元の合成比較の自然性を得る。
方針：全関手圏の指定同型の射と実合成を保持する。
規約：新しい比較を選ばない。使われ方：元の source graph・入力制限比較の自然性。
-/
@[expose] public section
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory SSet
lemma functorIso_trans_hom_square {S T : SSet.{u}} {f0 f1 g0 g1 h0 h1 : S ⟶ T}
    (c0 : FunctorIso f0 g0) (c1 : FunctorIso f1 g1)
    (d0 : FunctorIso g0 h0) (d1 : FunctorIso g1 h1)
    (x : FunctorHom f0 f1) (y : FunctorHom g0 g1) (z : FunctorHom h0 h1)
    (hc : c0.hom ≫ y = x ≫ c1.hom) (hd : d0.hom ≫ z = y ≫ d1.hom) :
    (c0 ≪≫ d0).hom ≫ z = x ≫ (c1 ≪≫ d1).hom := by
  simp only [Iso.trans_hom]
  calc
    (c0.hom ≫ d0.hom) ≫ z = c0.hom ≫ (d0.hom ≫ z) := Category.assoc _ _ _
    _ = c0.hom ≫ (y ≫ d1.hom) := congrArg (fun t => c0.hom ≫ t) hd
    _ = (c0.hom ≫ y) ≫ d1.hom := (Category.assoc _ _ _).symm
    _ = (x ≫ c1.hom) ≫ d1.hom := congrArg (fun t => t ≫ d1.hom) hc
    _ = x ≫ (c1.hom ≫ d1.hom) := Category.assoc _ _ _
end SerrePositivity.InfinityCategories
