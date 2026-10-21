module

public import SerrePositivity.InfinityCategories.F2.CoherentColimitUnitSquare
public import SerrePositivity.InfinityCategories.F1.FunctorSpaceCurrying

/-!
概要：全 coherent 図式上で、選択済み余錐の単位の自然性を一つの全族に束ねる。
方針：元の join 円柱に沿う制限を二重 curry し、任意のパラメータに制限する。
規約：選択済み余錐と元の辺の単位正方形を保持。使われ方：二単体の単位三角柱。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 元の余錐の全族から、その全単位を同時に読み出す時間付きの族。 -/
def coconeUnitFamily {K X T : SSet.{u}}
    (q : T ⟶ (ihom (join K (Δ[0] : SSet.{u}))).obj X) :
    T ⊗ (Δ[1] : SSet.{u}) ⟶ (ihom K).obj X :=
  (β_ T Δ[1]).hom ≫ uncurry (q ≫ (pre (coconeUnitCylinderMap K)).app X ≫
    functorSpaceCurryMap K Δ[1] X)

/-- 全単位の族は、元の余錐の任意のパラメータへの制限と厳密に可換。 -/
lemma coconeUnitFamily_precomp {K X T P : SSet.{u}}
    (q : T ⟶ (ihom (join K (Δ[0] : SSet.{u}))).obj X) (t : P ⟶ T) :
    (t ▷ (Δ[1] : SSet.{u})) ≫ coconeUnitFamily q = coconeUnitFamily (t ≫ q) := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro p
  apply CategoryTheory.Functor.functorHom_ext
  intro d α
  apply ConcreteCategory.hom_ext
  intro k
  rfl

/-- 全 coherent 図式に対する、元の余極限単位の自然性の全族。 -/
def coherentColimitUnitFamily (B : SSet.{u}) :=
  coconeUnitFamily (coherentColimitCoconeFunctor B)

/-- 元の関手辺への制限は、既存の同じ全単位正方形そのもの。 -/
lemma coherentColimitUnitFamily_edge (B : SSet.{u})
    {F G : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}}
    (H : SSet.Homotopy F G) :
    (curry H.h ▷ (Δ[1] : SSet.{u + 1})) ≫ coherentColimitUnitFamily B =
      (β_ Δ[1] Δ[1]).hom ≫ coherentColimitUnitSquare B H := by
  change _ = (β_ Δ[1] Δ[1]).hom ≫ curry (_ ≫ ((coconeUnitCylinderMap _ ▷ Δ[1]) ≫
    (coherentColimitCoconeHomotopy B H).h))
  rw [coherentColimitCoconeHomotopy_h]
  apply uncurry_injective
  simp only [uncurry_natural_left, uncurry_curry]
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro p
  rfl

end SerrePositivity.InfinityCategories.F2
