module


public import Mathlib.AlgebraicTopology.ModelCategory.CategoryWithCofibrations
public import Mathlib.AlgebraicTopology.SimplexCategory.Defs
public import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.PushoutProduct
public import Mathlib.AlgebraicTopology.SimplicialSet.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.CategoryWithFibrations
public import Mathlib.AlgebraicTopology.SimplicialSet.KanComplex
public import Mathlib.Basic.Opposite
public import Mathlib.Basic.UnivLE
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Category.Basic
public import Mathlib.CategoryTheory.Discrete.Basic
public import Mathlib.CategoryTheory.FinCategory.Basic
public import Mathlib.CategoryTheory.Functor.Basic
public import Mathlib.CategoryTheory.Functor.Category
public import Mathlib.CategoryTheory.LiftingProperties.Basic
public import Mathlib.CategoryTheory.LiftingProperties.ParametrizedAdjunction
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.Finite
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts.WalkingPair
public import Mathlib.CategoryTheory.Limits.Shapes.FiniteProducts
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Cospan
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.PullbackObjObj
public import Mathlib.CategoryTheory.Limits.Shapes.Terminal
public import Mathlib.CategoryTheory.Limits.Shapes.WidePullbacks
public import Mathlib.CategoryTheory.Limits.Types.Colimits
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
public import Mathlib.CategoryTheory.Monoidal.Cartesian.FunctorCategory
public import Mathlib.CategoryTheory.Monoidal.Category
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.FunctorToTypes
public import Mathlib.CategoryTheory.Monoidal.FunctorCategory
public import Mathlib.CategoryTheory.Monoidal.Types.Basic
public import Mathlib.CategoryTheory.MorphismProperty.Basic
public import Mathlib.CategoryTheory.MorphismProperty.LiftingProperty
public import Mathlib.CategoryTheory.NatTrans
public import Mathlib.CategoryTheory.Opposites
public import Mathlib.CategoryTheory.Types.Basic
public import Mathlib.Combinatorics.Quiver.Basic
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Fintype.OfMap

/-!
分割で生成：docstring を書き直すこと
概要：anodyne な基点包含からの点つき Hom の全境界充填。
方針：pushout-product と指数の随伴で全ての単射に対する右持ち上げ性を移す。
規約：終対象への射の RLP として全境界充填を表す。
使われ方：Goerss–Jardine I §7、Kerodon §3.1.3（Tag 00TJ）。path の零次数の比較。

対応節は Kerodon 3.1（Tag 00SZ）。
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory
open SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen

namespace SerrePositivity.KST.Spectra
end SerrePositivity.KST.Spectra
namespace SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open _root_.SerrePositivity.KST.Spectra

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：anodyne な射による Kan 標的への指数の制限は全ての単射に RLP を持つ。
方針：単射との pushout-product の anodyne 性とパラメータ付き随伴を使う。
規約：全ての単射についての右持ち上げ性を述べる。
使われ方：Kerodon §3.1.3（Tag 00TJ）、Goerss–Jardine I §7。path space の全境界充填。 -/
theorem anodyne_pre_rlp_monomorphisms {A B : SSet.{u}} (i : A ⟶ B)
    (hi : anodyneExtensions i) (Y : SSet.{u}) [KanComplex Y] :
    (MorphismProperty.monomorphisms SSet.{u}).rlp ((MonoidalClosed.pre i).app Y) := by
  intro S T j hj
  let : Mono j := hj
  let sq₁₂ := Functor.PushoutObjObj.ofHasPushout (curriedTensor SSet.{u}) i j
  let sq₁₃ := Functor.PullbackObjObj.ofIsTerminal MonoidalClosed.internalHom
    i (terminal.from Y) terminalIsTerminal
  change HasLiftingProperty j sq₁₃.π
  rw [← internalHomAdjunction₂.hasLiftingProperty_iff sq₁₂ sq₁₃]
  exact (anodyneExtensions_pushoutObjObjι' sq₁₂ hi) (terminal.from Y)
    ((HomotopicalAlgebra.fibration_iff _).mp inferInstance)

end

end SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section
