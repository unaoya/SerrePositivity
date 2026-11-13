module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.PinchedModels.PinchedLinearChainMap
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StandardComposition
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.FunctorMapping
/-!
概要：dg 関手と Hom 鎖写像の標準 DK 単体への作用を構成する。
方針：線形単体との符号同値を共役し、全成分で係数写像を計算する。
規約：対象の Small 性を仮定せず、元の全次数と二入力を保持する。
使われ方：coherent 合成 prism の dg 関手自然性の係数計算。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
open scoped _root_.Simplicial
variable {A : Type u} [CommRing A] {D E : Type v} [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [_root_.SerrePositivity.DifferentialGraded.DGCategory A E]

def dgStandardSimplexMap {x y : D} {x' y' : E}
    (φ : _root_.SerrePositivity.DifferentialGraded.homObject A D x y ⟶ _root_.SerrePositivity.DifferentialGraded.homObject A E x' y') {n : ℕ}
    (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StandardSimplex A x y n) : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StandardSimplex A x' y' n :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardSimplexEquiv x' y' n
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedLinearSimplexMap φ ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardSimplexEquiv x y n).symm s))

lemma dgStandardSimplexMap_component {x y : D} {x' y' : E}
    (φ : _root_.SerrePositivity.DifferentialGraded.homObject A D x y ⟶ _root_.SerrePositivity.DifferentialGraded.homObject A E x' y') {n : ℕ}
    (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StandardSimplex A x y n) (J : Finset (Fin (n + 1))) (k : ℤ)
    (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ)) :
    (dgStandardSimplexMap φ s).val.component J k hJ hk =
      φ.f k (s.val.component J k hJ hk) := by
  change _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.degreeSign (J.card - 1) •
    (φ.f k (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.degreeSign (J.card - 1) • s.val.component J k hJ hk)) = _
  rw [map_zsmul, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.degreeSign_smul_involutive]

lemma dgStandardSimplexMap_aw (Q : _root_.SerrePositivity.DifferentialGraded.DGFunctor A D E) {x y z : D} {n : ℕ}
    (g : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StandardSimplex A y z n) (f : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StandardSimplex A x y n) :
    dgStandardSimplexMap (Q.map x z) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardAW g f) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardAW (dgStandardSimplexMap (Q.map y z) g)
        (dgStandardSimplexMap (Q.map x y) f) := by
  apply Subtype.ext
  funext i
  rcases i with ⟨⟨J, k⟩, hJ, hk⟩
  change (dgStandardSimplexMap (Q.map x z) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardAW g f)).val.component J k hJ hk = _
  rw [dgStandardSimplexMap_component]
  change (Q.map x z).f k ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awData g.val f.val).component J k hJ hk) =
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awData (dgStandardSimplexMap (Q.map y z) g).val
      (dgStandardSimplexMap (Q.map x y) f).val).component J k hJ hk
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awData_component, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awData_component, map_sum]
  apply Finset.sum_congr rfl
  intro j _
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awTerm
  rw [dgStandardSimplexMap_component, dgStandardSimplexMap_component]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.map_compose Q _ _ _
end SerrePositivity.InfinityCategories.Project.DerivedCategories
