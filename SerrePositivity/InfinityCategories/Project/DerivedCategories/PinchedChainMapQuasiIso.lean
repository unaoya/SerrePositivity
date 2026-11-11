module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.PinchedComplexModelComparison
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.ComplexPinchedQuasiIso

/-! # 実 dg 写像空間の一般準同型不変性

概要：全射性を仮定しない Hom 鎖準同型は、実 pinched 空間のホモトピー同値。
方針：複体の単位 Hom 模型で全射 span を使い、実比較同型を介して戻す。
規約：任意可換環、対象宇宙は同じ。使われ方：β3 の局所 Hom と β5 の準同値。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable {A : Type u} [CommRing A] {D E : Type v} [DGCategory A D] [DGCategory A E]
variable {x y : D} {x' y' : E}

/-- 一般の Hom 鎖準同型が誘導する実 pinched 写像はホモトピー同値。 -/
theorem pinchedHomChainMap_quasiIso_equivalence
    (φ : homObject A D x y ⟶ homObject A E x' y') [QuasiIso φ] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap φ) := by
  have hm := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap_quasiIso_equivalence.{u, v} φ).isQCatEquivalence
  have hi := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedComplexModelIso x y)).isQCatEquivalence.comp hm
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedComplexModelIso x y).hom ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap.{u, v} φ) at hi
  rw [← _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedComplexModelIso_naturality] at hi
  have hc := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedComplexModelIso x' y')).isQCatEquivalence.cancel_right hi
  exact hc.isSimplicialHomotopyEquivalence

end SerrePositivity.InfinityCategories.Project.DerivedCategories
