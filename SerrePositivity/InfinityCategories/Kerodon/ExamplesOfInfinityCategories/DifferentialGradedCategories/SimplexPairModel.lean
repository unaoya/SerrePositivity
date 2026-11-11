module
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.LinearizedSpace
public import Mathlib.AlgebraicTopology.ExtraDegeneracy

/-!
# AW/shuffle 比較の普遍単体模型

概要：二つの単体射の対を単体的集合とし、先頭頂点0の付加による収縮を作る。
方針：標準単体の extra degeneracy を各座標に同時に適用する。
規約：KST Construction A.5 の標準比較を再帰で実現する模型。非被約。
使われ方：比較の差を普遍模型で埋め、任意の二つの加群の単体へ評価する。

対応節は Kerodon 2.5（Tag 00ND）。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
open CategoryTheory Opposite
open scoped Simplicial

/-- 概要：二つの N 単体上の普遍な対の単体的集合。
方針：各次数の二つの単体射の対を取り、前合成で単体構造を定める。
規約：KST A.5、ULift は加群の宇宙を揃えるためだけに用いる。
使われ方：標準比較ホモトピーの有限な普遍鎖。 -/
def simplexPairModel (N : ℕ) : SSet.{u} where
  obj r := ULift.{u} ((r.unop ⟶ ⦋N⦌) × (r.unop ⟶ ⦋N⦌))
  map f := ↾fun z ↦ ⟨(f.unop ≫ z.down.1, f.unop ≫ z.down.2)⟩
  map_id r := by
    apply ConcreteCategory.hom_ext
    intro z
    simp only [unop_id, Category.id_comp]
    rfl
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    intro z
    simp only [unop_comp, Category.assoc]
    rfl

/-- 概要：普遍な対の模型を一点へ増大する。
方針：全ての対を唯一の点へ送る。
規約：KST A.5、増大を持つ非被約模型。
使われ方：零次の増大を含む収縮。 -/
def augmentedSimplexPairModel (N : ℕ) : SimplicialObject.Augmented (Type u) where
  left := simplexPairModel N
  right := PUnit.{u + 1}
  hom := { app := fun _ ↦ ↾fun _ ↦ PUnit.unit }

/-- 概要：普遍な対の模型の先頭頂点による extra degeneracy。
方針：二つの単体射に標準単体の shift を同時に適用する。
規約：KST Construction A.5 の標準比較、両座標の頂点は0。
使われ方：普遍な正次数サイクルを明示的に埋める収縮。 -/
def simplexPairExtraDegeneracy (N : ℕ) :
    SimplicialObject.Augmented.ExtraDegeneracy (augmentedSimplexPairModel.{u} N) where
  s' := ↾fun _ ↦ ⟨(SimplexCategory.Hom.mk (OrderHom.const _ 0),
    SimplexCategory.Hom.mk (OrderHom.const _ 0))⟩
  s n := ↾fun z ↦ ⟨(SSet.Augmented.StandardSimplex.shift z.down.1,
    SSet.Augmented.StandardSimplex.shift z.down.2)⟩
  s'_comp_ε := by
    apply ConcreteCategory.hom_ext
    intro x
    change (PUnit.unit : PUnit.{u + 1}) = x
    exact Subsingleton.elim _ _
  s₀_comp_δ₁ := by
    apply ConcreteCategory.hom_ext
    intro z
    apply ULift.ext
    apply Prod.ext <;> apply SimplexCategory.Hom.ext <;> ext j <;> fin_cases j <;> rfl
  s_comp_δ₀ n := by
    apply ConcreteCategory.hom_ext
    intro z
    apply ULift.ext
    apply Prod.ext <;> apply SimplexCategory.Hom.ext <;> ext j <;> rfl
  s_comp_δ n i := by
    apply ConcreteCategory.hom_ext
    intro z
    apply ULift.ext
    apply Prod.ext <;> apply SimplexCategory.Hom.ext <;> ext j
    all_goals
      cases j using Fin.cases <;>
        simp [SimplicialObject.δ, simplexPairModel, augmentedSimplexPairModel,
          SSet.Augmented.StandardSimplex.shift, SimplexCategory.δ,
          SSet.Augmented.StandardSimplex.shiftFun]
  s_comp_σ n i := by
    apply ConcreteCategory.hom_ext
    intro z
    apply ULift.ext
    apply Prod.ext <;> apply SimplexCategory.Hom.ext <;> ext j
    all_goals
      cases j using Fin.cases <;>
        simp [SimplicialObject.σ, simplexPairModel, augmentedSimplexPairModel,
          SSet.Augmented.StandardSimplex.shift, SimplexCategory.σ,
          SSet.Augmented.StandardSimplex.shiftFun]

/-- 概要：普遍模型の二つの標的単体射を後合成で変える。
方針：対の各成分へ独立に後合成する。
規約：KST A.5、二つの標的の次数はここでは同じ。
使われ方：普遍鎖を単体の面へ移す。 -/
def simplexPairModelMap {N M : ℕ} (f g : ⦋N⦌ ⟶ ⦋M⦌) :
    simplexPairModel.{u} N ⟶ simplexPairModel.{u} M where
  app r := ↾fun z ↦ ⟨(z.down.1 ≫ f, z.down.2 ≫ g)⟩
  naturality _ _ h := by
    apply ConcreteCategory.hom_ext
    intro z
    apply ULift.ext
    exact Prod.ext (Category.assoc _ _ _) (Category.assoc _ _ _)

/-- 概要：増大した普遍模型を自由整数加群へ移す。
方針：自由化関手の右 whisker を適用する。
規約：KST A.5、増大は保持する。
使われ方：正次数の鎖収縮の実模型。 -/
def linearizedAugmentedSimplexPairModel (N : ℕ) :
    SimplicialObject.Augmented (ModuleCat.{u} ℤ) :=
  ((SimplicialObject.Augmented.whiskering _ _).obj integerLinearization).obj
    (augmentedSimplexPairModel N)

/-- 概要：自由化した普遍模型も同じ先頭頂点の収縮を持つ。
方針：extra degeneracy の関手による移送を使う。
規約：KST A.5、追加の可縮性仮定を導入しない。
使われ方：標準比較ホモトピーの再帰で普遍サイクルを充填する。 -/
def simplexPairLinearExtraDegeneracy (N : ℕ) :
    SimplicialObject.Augmented.ExtraDegeneracy (linearizedAugmentedSimplexPairModel.{u} N) :=
  (simplexPairExtraDegeneracy N).map integerLinearization

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
