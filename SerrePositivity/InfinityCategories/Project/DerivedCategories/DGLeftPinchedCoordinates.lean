module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGLeftPinchedChainMap
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LeftHomEnrichedNaturality
/-!
概要：左 pinched Hom の反対模型同型と coslice fiber 同型の、実全単体の座標を計算する。
方針：端点輸送を消去し、同じ反対 dg 単体と同じ join 単体を回収する。
規約：全次数の実等式。使われ方：閉始点前合成と実 fiber 射の照合。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] (x y : D)
/-- 同じ左 Hom の反対模型同型は、元の実全単体の符号付き反転である。 -/
lemma dgLeftPinchedOppositeIso_hom_val {n : ℕ}
    (s : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomLeft (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R D) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex y)) _⦋n⦌) :
    (SSet.opObjEquiv ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLeftPinchedOppositeIso R D x y).hom.app _ s)).val =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.opSimplex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedLeftSimplexVal n s) := by
  change ((eqToHom (congrArg₂ (fun a b ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom
    (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R Dᵒᵖ) a b)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveOppositeIso_hom_vertex R D y) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveOppositeIso_hom_vertex R D x))).app _
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomMap (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveOppositeIso R D).hom
        (SSet.opObjEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex y))
        (SSet.opObjEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x))).app _ (SSet.opObjEquiv s))).val = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHom_eqToHom_app_val (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveOppositeIso_hom_vertex R D y)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveOppositeIso_hom_vertex R D x)]
  rfl
/-- 左 Hom の同じ coslice fiber 同型は、元の同じ全単体を保つ。 -/
lemma dgLeftPinchedCosliceFiberIso_simplex {X : SSet.{w}}
    (a b : X _⦋0⦌) {n : ℕ} (s : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomLeft a b) _⦋n⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.cosliceFiberSimplex n ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedLeftCosliceFiberIso a b).hom.app _ s) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedLeftSimplexVal n s := by
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.cosliceFiberSimplex n ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.cosliceFiberSimplexEquiv a b n).symm
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedLeftSimplexEquiv a b n) s)) = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.cosliceFiberSimplex_equiv_symm]
  rfl
end SerrePositivity.InfinityCategories.Project.DerivedCategories
