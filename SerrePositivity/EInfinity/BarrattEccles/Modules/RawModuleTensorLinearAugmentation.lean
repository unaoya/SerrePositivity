module
public import SerrePositivity.EInfinity.BarrattEccles.Modules.RawModuleTensorConeAugmentation
public import SerrePositivity.EInfinity.Modules.ClosedPostcomposition
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.PinchedModels.PinchedClosedVertexNaturality

/-!
概要：元の実 augmentation は普遍 cochain の全正次成分を零に送る。
方針：同じ恒等辺の定値単体の線形表示を使い、非単射引き戻しの成分を消す。
規約：任意の二点以上の部分集合と元の実 augmentation を保持する。
使われ方：大域 prism の augmentation 合成が恒等円柱となる成分式。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories

open SerrePositivity.InfinityCategories.HA.Section7_1_1
open SerrePositivity.InfinityCategories.Project.DerivedCategories
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
open SerrePositivity.EInfinity.Modules SerrePositivity.EInfinity.ComplexLimits
open scoped Simplicial
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

lemma strictRawModuleTensorElementLinear_augmentation {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedLinearSimplexMap (D := RightModule A (dgAlgebraCategory A ((assocForget A).obj X))) (E := RightModule A (dgAlgebraCategory A ((assocForget A).obj X))) (x := ForgetEnrichment.to (Complex A) ((strictRawModuleProbeFunctor A X).obj P)) (x' := ForgetEnrichment.to (Complex A) ((strictRawModuleProbeFunctor A X).obj P))
      (eHomWhiskerLeft (Complex A) ((strictRawModuleProbeFunctor A X).obj P)
        ((strictRawModuleTensorElementAugmentation A X P Q).app (c.obj (Fin.last n))))
      (strictRawModuleTensorElementLinear A X P Q c) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearSimplex.pullback (SimplexCategory.const ⦋n⦌ ⦋0⦌ 0).toOrderHom
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.toLinearSimplex (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedClosedVertex A (RightModule A (dgAlgebraCategory A ((assocForget A).obj X))) (𝟙 ((strictRawModuleProbeFunctor A X).obj P)))) := by
  have h := congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.toLinearSimplex (A := A) (D := RightModule A (dgAlgebraCategory A ((assocForget A).obj X))) (x := ForgetEnrichment.to (Complex A) ((strictRawModuleProbeFunctor A X).obj P)) (y := ForgetEnrichment.to (Complex A) ((strictRawModuleProbeFunctor A X).obj P)))
    (strictRawModuleTensorElementPinchedSimplex_augmentation_identity A X P Q c)
  exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMapSimplex_linear _ _).symm.trans
    (h.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.toLinearSimplex_pullback _ _))

lemma strictRawModuleTensorElementLinear_augmentation_zero {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n)
    (J : Finset (Fin (n + 1))) (k : ℤ) (hJ : 2 ≤ J.card) (hk : k = 1 - (J.card : ℤ)) :
    (eHomWhiskerLeft (Complex A) ((strictRawModuleProbeFunctor A X).obj P)
      ((strictRawModuleTensorElementAugmentation A X P Q).app (c.obj (Fin.last n)))).f k
      ((strictRawModuleTensorElementLinear A X P Q c).val.component J k
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hJ) hk) = 0 := by
  have h := congrArg (fun s : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearSimplex A (ForgetEnrichment.to (Complex A) ((strictRawModuleProbeFunctor A X).obj P)) (ForgetEnrichment.to (Complex A) ((strictRawModuleProbeFunctor A X).obj P)) n =>
      s.val.component J k (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hJ) hk)
    (strictRawModuleTensorElementLinear_augmentation A X P Q c)
  exact h.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pullback_component_of_not_inj (A := A) (D := RightModule A (dgAlgebraCategory A ((assocForget A).obj X)))
    (x := ForgetEnrichment.to (Complex A) ((strictRawModuleProbeFunctor A X).obj P)) (y := ForgetEnrichment.to (Complex A) ((strictRawModuleProbeFunctor A X).obj P)) _ _ J k (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hJ) hk (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.not_injOn_constant hJ))

end SerrePositivity.EInfinity.BarrattEccles
