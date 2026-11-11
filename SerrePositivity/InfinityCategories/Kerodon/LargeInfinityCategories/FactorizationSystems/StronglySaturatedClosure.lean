module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FactorizationSystems.LocalStrongSaturation
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：小添字の宇宙を指定した強飽和生成閉包と局所同値との比較。
方針：全ての強飽和な上集合の共通部分を取り、局所同値の強飽和性を使う。
規約：生成閉包と局所同値の一致・小生成性・反射の存在は同一視しない。
使われ方：HTT 5.5.4 の小生成な強飽和類の構成。

対応節は Kerodon 9.6（Tag 04KF）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FactorizationSystems
variable {X : SSet.{v}} [Quasicategory X]

/-- 指定された小形状について、元の辺集合が生成する最小の強飽和類。 -/
@[kerodon 06XK]
def stronglySaturatedClosure (smallShape : SSet.{u} → SSet.{v})
    (W : Set (X _⦋1⦌)) : Set (X _⦋1⦌) :=
  {e | ∀ S : Set (X _⦋1⦌), _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FactorizationSystems.IsStronglySaturatedEdgeSetOfShapes smallShape S → W ⊆ S → e ∈ S}

/-- 元の辺集合は、その強飽和生成閉包に含まれる。 -/
lemma subset_stronglySaturatedClosure (smallShape : SSet.{u} → SSet.{v})
    (W : Set (X _⦋1⦌)) : W ⊆ stronglySaturatedClosure smallShape W :=
  fun _ he _ _ hW ↦ hW he

/-- 強飽和生成閉包は、元の辺集合を含む全ての強飽和類に含まれる。 -/
lemma stronglySaturatedClosure_minimal (smallShape : SSet.{u} → SSet.{v})
    {W S : Set (X _⦋1⦌)} (hS : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FactorizationSystems.IsStronglySaturatedEdgeSetOfShapes smallShape S)
    (hW : W ⊆ S) : stronglySaturatedClosure smallShape W ⊆ S :=
  fun _ he ↦ he S hS hW

/-- 強飽和生成閉包は生成する辺集合について単調。 -/
lemma stronglySaturatedClosure_mono (smallShape : SSet.{u} → SSet.{v})
    {W V : Set (X _⦋1⦌)} (h : W ⊆ V) :
    stronglySaturatedClosure smallShape W ⊆ stronglySaturatedClosure smallShape V :=
  fun _ he S hS hV ↦ he S hS (h.trans hV)

/-- 強飽和生成閉包は、元の pushout・余極限・二単体に関して強飽和。 -/
lemma stronglySaturatedClosure_stronglySaturated (smallShape : SSet.{u} → SSet.{v})
    (W : Set (X _⦋1⦌)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FactorizationSystems.IsStronglySaturatedEdgeSetOfShapes smallShape (stronglySaturatedClosure smallShape W) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x y e he S hS _
    exact hS.1 e he
  · intro R hR he S hS hW
    exact hS.2.1 R hR (he S hS hW)
  · intro K r c hc hvertices S hS hW
    exact hS.2.2.1 K r c hc (fun k ↦ hvertices k S hS hW)
  · intro x y z e01 e12 e02 t h01 h12 S hS hW
    exact hS.2.2.2.1 t (h01 S hS hW) (h12 S hS hW)
  · intro x y z e01 e12 e02 t h01 h02 S hS hW
    exact hS.2.2.2.2.1 t (h01 S hS hW) (h02 S hS hW)
  · intro x y z e01 e12 e02 t h12 h02 S hS hW
    exact hS.2.2.2.2.2 t (h12 S hS hW) (h02 S hS hW)

/-- 強飽和生成閉包は冪等。 -/
lemma stronglySaturatedClosure_idempotent (smallShape : SSet.{u} → SSet.{v})
    (W : Set (X _⦋1⦌)) :
    stronglySaturatedClosure smallShape (stronglySaturatedClosure smallShape W) =
      stronglySaturatedClosure smallShape W :=
  Set.Subset.antisymm (stronglySaturatedClosure_minimal smallShape
    (stronglySaturatedClosure_stronglySaturated smallShape W) (Set.Subset.refl _))
    (subset_stronglySaturatedClosure smallShape _)

/-- 既に強飽和な類は、その強飽和生成閉包と一致する。 -/
lemma stronglySaturatedClosure_eq_self (smallShape : SSet.{u} → SSet.{v})
    {S : Set (X _⦋1⦌)} (hS : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FactorizationSystems.IsStronglySaturatedEdgeSetOfShapes smallShape S) :
    stronglySaturatedClosure smallShape S = S :=
  Set.Subset.antisymm (stronglySaturatedClosure_minimal smallShape hS (Set.Subset.refl _))
    (subset_stronglySaturatedClosure smallShape S)

/-- 小ささは生成元の添字の宇宙で指定し、強飽和類全体の小ささは要求しない。 -/
def IsOfSmallStrongGeneration (smallShape : SSet.{u} → SSet.{v})
    (S : Set (X _⦋1⦌)) : Prop :=
  ∃ (I : Type u) (edges : I → X _⦋1⦌), S = stronglySaturatedClosure smallShape (Set.range edges)

/-- 小さい族から生成した強飽和類は、同じ小さい族で小生成。 -/
lemma stronglySaturatedClosure_range_smallGeneration (smallShape : SSet.{u} → SSet.{v})
    {I : Type u} (edges : I → X _⦋1⦌) :
    IsOfSmallStrongGeneration smallShape (stronglySaturatedClosure smallShape (Set.range edges)) :=
  ⟨I, edges, rfl⟩

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FactorizationSystems
