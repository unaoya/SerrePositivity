module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.PinchedHomChainMap
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.EquivalenceCalculus

/-! # pinched 写像空間の鎖写像に関する関手則

概要：Hom 鎖写像による実 pinched 写像は恒等と合成を保ち、鎖同型を実同型に送る。
方針：実単体の線形表示で全成分を照合する。
規約：異なる dg 圏の固定 Hom 同士を扱う。使われ方：一般準同型の全射 span 比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
open scoped _root_.Simplicial
variable {A : Type u} [CommRing A] {D E T : Type v}
  [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [_root_.SerrePositivity.DifferentialGraded.DGCategory A E] [_root_.SerrePositivity.DifferentialGraded.DGCategory A T]
variable {x y : D} {x' y' : E} {x'' y'' : T}

/-- 恒等 Hom 鎖写像が誘導する実 pinched 写像は恒等。 -/
lemma pinchedHomChainMap_id :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap (𝟙 (homObject A D x y)) = 𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A D x y) := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro s
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.linearEquiv x y n.unop.len).injective
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.toLinearSimplex (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMapSimplex _ s) = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.toLinearSimplex s
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMapSimplex_linear]
  apply Subtype.ext
  rfl

/-- Hom 鎖写像の合成が誘導する実 pinched 写像は実際の合成。 -/
lemma pinchedHomChainMap_comp
    (φ : _root_.SerrePositivity.DifferentialGraded.homObject A D x y ⟶ _root_.SerrePositivity.DifferentialGraded.homObject A E x' y')
    (ψ : _root_.SerrePositivity.DifferentialGraded.homObject A E x' y' ⟶ _root_.SerrePositivity.DifferentialGraded.homObject A T x'' y'') :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap (φ ≫ ψ) = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap φ ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap ψ := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro s
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.linearEquiv x'' y'' n.unop.len).injective
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.toLinearSimplex (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMapSimplex _ s) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.toLinearSimplex (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMapSimplex ψ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMapSimplex φ s))
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMapSimplex_linear, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMapSimplex_linear]
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMapSimplex_linear]
  apply Subtype.ext
  rfl

/-- Hom 複体の実同型は実 pinched 写像空間の同型を誘導する。 -/
lemma pinchedHomChainMap_isIso
    (φ : _root_.SerrePositivity.DifferentialGraded.homObject A D x y ⟶ _root_.SerrePositivity.DifferentialGraded.homObject A E x' y') [IsIso φ] :
    IsIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap φ) := by
  let e : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A D x y ≅ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A E x' y' := {
    hom := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap φ
    inv := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap (inv φ)
    hom_inv_id := by rw [← pinchedHomChainMap_comp, IsIso.hom_inv_id, pinchedHomChainMap_id]
    inv_hom_id := by rw [← pinchedHomChainMap_comp, IsIso.inv_hom_id, pinchedHomChainMap_id] }
  exact e.isIso_hom

end SerrePositivity.InfinityCategories.Project.DerivedCategories
