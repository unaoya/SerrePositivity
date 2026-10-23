module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.NervePresentationComparison
public import SerrePositivity.InfinityCategories.F1.UniverseOverFunctor
public import SerrePositivity.InfinityCategories.F1.ContravariantComparisonIso

/-!
概要：表示同型で移した元の全局所 Hom 比較の、同じ底上の射に沿う自然性。
方針：元の局所比較の指定同型を両側の反変図式の表示同型で運ぶ。
規約：全局所 Hom と元の指定同型を使う。
使われ方：標準セルの比較を共有境界へ制限する自然性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories
variable {A D C : Type u} [Category.{u} A] [Category.{u} D] [Category.{u} C]
  (l : A ⥤ D) (k : D ⥤ C) (p q : CocartesianFibrationCategory (nerve C))
local notation "N" => (cocartesianPullbackNativeCoreFunctor p.val.hom q.val.hom) ⋙
  SSet.uliftFunctor
local notation "T" => Functor.op (uliftOverFunctor (nerve C)) ⋙
  intervalDiagramOverFunctor (cocartesianStrictTransportCoherentDiagram p.val.hom)
    (cocartesianStrictTransportCoherentDiagram q.val.hom)

local instance (z : (Over (nerve C))ᵒᵖ) : Quasicategory ((T).obj z) :=
  inferInstanceAs (Quasicategory (intervalMappingSpace
    (functorVertex ((SSet.uliftFunctor.{u + 1, u}).map z.unop.hom ≫
      cocartesianStrictTransportCoherentDiagram p.val.hom))
    (functorVertex ((SSet.uliftFunctor.{u + 1, u}).map z.unop.hom ≫
      cocartesianStrictTransportCoherentDiagram q.val.hom))))

/-- 元の局所比較の指定自然性を、同じ native 図式の表示で回収する。 -/
def cocartesianNerveNativeHomComparison_naturalityIso :
    FunctorIso
      ((N).map (cocartesianBaseChangeOverMap l k).op ≫
        cocartesianNerveNativeHomComparison (l ⋙ k) p q)
      (cocartesianNerveNativeHomComparison k p q ≫
        (T).map (cocartesianBaseChangeOverMap l k).op) :=
  cocartesianLocalHomComparison_overNaturalityIso l k p q

/-- 同じ表示同型で移した比較は、元の底上の射に沿って自然。 -/
def cocartesianNervePresentationHomComparison_naturalityIso
    {a b : Over (nerve C)} (ea : a ≅ Over.mk (nerveMap (l ⋙ k)))
    (eb : b ≅ Over.mk (nerveMap k)) (f : a ⟶ b)
    (h : ea.hom ≫ cocartesianBaseChangeOverMap l k = f ≫ eb.hom) :
    FunctorIso
      ((N).map f.op ≫ cocartesianNervePresentationHomComparison a (l ⋙ k) ea p q)
      (cocartesianNervePresentationHomComparison b k eb p q ≫ (T).map f.op) :=
  contravariantComparisonIso (N) (T) ea eb f (cocartesianBaseChangeOverMap l k) h
    (cocartesianNerveNativeHomComparison (l ⋙ k) p q)
    (cocartesianNerveNativeHomComparison k p q)
    (cocartesianNerveNativeHomComparison_naturalityIso l k p q)

end SerrePositivity.InfinityCategories
