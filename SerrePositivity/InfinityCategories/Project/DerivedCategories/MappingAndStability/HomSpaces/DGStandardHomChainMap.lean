module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Homotopies.DGComparisons.DGStandardSimplexMap
/-!
概要：Hom 鎖写像を標準 DK 写像空間の実単体的写像へ送る。
方針：標準座標との符号同値で pinched 線形作用を共役する。
規約：対象の Small 性を仮定せず、すべての面と退化を保つ。
使われ方：D-8 c5 の実写像空間の積の比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DGStandardHomChainMap
open CategoryTheory DifferentialGraded
variable {R : Type u} [CommRing R] {D E : Type v} [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [_root_.SerrePositivity.DifferentialGraded.DGCategory R E]

lemma dgStandardSimplexMap_pullback {x y : D} {a b : E}
    (φ : _root_.SerrePositivity.DifferentialGraded.homObject R D x y ⟶ _root_.SerrePositivity.DifferentialGraded.homObject R E a b) {m n : ℕ}
    (α : Fin (m + 1) →o Fin (n + 1)) (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StandardSimplex R x y n) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStandardSimplexMap φ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardPullback α s) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardPullback α (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStandardSimplexMap φ s) := by
  unfold _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStandardSimplexMap _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardPullback
  simp only [LinearEquiv.coe_toLinearMap, LinearEquiv.symm_apply_apply,
    LinearMap.comp_apply]
  congr 1
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedLinearSimplexMap_pullback φ α _

def dgStandardHomChainMap {x y : D} {a b : E}
    (φ : _root_.SerrePositivity.DifferentialGraded.homObject R D x y ⟶ _root_.SerrePositivity.DifferentialGraded.homObject R E a b) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardHomSpace (R := R) x y ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardHomSpace (R := R) a b where
  app _ := ↾(_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStandardSimplexMap φ)
  naturality {m n} α := by
    apply ConcreteCategory.hom_ext
    intro s
    exact dgStandardSimplexMap_pullback φ α.unop.toOrderHom s

end SerrePositivity.InfinityCategories.Project.DerivedCategories.DGStandardHomChainMap
