module
public import SerrePositivity.InfinityCategories.Derived.DeformationDescentHomNaturality
public import SerrePositivity.InfinityCategories.Derived.FunctorHomWhiskering
/-!
概要：同じ変形降下の自然性を、明示した始域と終域の全関手射で表す。
方針：一般の全関手圏で同じ射の等式を証明し、指定値を保つ。
規約：可逆性は追加しない。使われ方：元の ξ と K-flat 合成比較の自然性。
-/
@[expose] public section
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory SSet MonoidalClosed
open scoped Simplicial
noncomputable section
lemma deformationComparisonIso_hom_naturality_typed {X D Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y]
    (L : X ⟶ D) (I : D ⟶ X) (W : Set (X _⦋1⦌))
    (H : SSet.Homotopy (L ≫ I) (𝟙 X))
    (hH : ∀ x, (simplicialHomotopyVertexEdge H x).edge ∈ W)
    (T U : X ⟶ Y) (hT : InvertsEdges T W) (hU : InvertsEdges U W)
    {K K' : D ⟶ Y} (r : FunctorIso K (I ≫ T)) (s : FunctorIso K' (I ≫ U))
    (b : FunctorHom K K') (a : FunctorHom T U)
    (hs : b ≫ s.hom = r.hom ≫
      functorHomPrecomp T U I a) :
    (r.precomp L ≪≫ deformationFunctorDescentIso L I W H hH T hT).hom ≫ a =
      functorHomPrecomp K K' L b ≫
        (s.precomp L ≪≫ deformationFunctorDescentIso L I W H hH U hU).hom := by
  exact deformationComparisonIso_hom_naturality L I W H hH T U hT hU r s b a hs
end
end SerrePositivity.InfinityCategories
