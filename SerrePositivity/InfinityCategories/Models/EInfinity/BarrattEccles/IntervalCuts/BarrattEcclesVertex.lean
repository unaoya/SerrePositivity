module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.Coalgebra
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.ZeroVertexValues
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ZeroAugmentation

/-!
模型。文献の定義との比較は後で
# 実際の E 余作用の零次頂点値

概要：Berger–Fresse §1.3・§3.1 の TR 制限後の区間余作用を BE augmentation で表す。
方針：係数の TR を評価し、χ の係数和と BE augmentation の零次整合性を使う。
規約：全 arity と任意の整数零次の BE 係数。
使われ方：端点・収縮の余代数射性の零次条件。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory _root_.HomologicalComplex
open _root_.SerrePositivity.DifferentialGraded

variable (A : Type u) [CommRing A]

/-- 概要：E の零次頂点余作用は実際の BE augmentation 倍の一定頂点（BF §3.1）。
方針：TR の右テンソル作用と χ の零次頂点値を評価して係数比較を使う。
規約：全 arity、任意の BE 零次係数と両頂点。
使われ方：区間の端点・収縮の実際の余作用保存。 -/
lemma barrattEcclesCoaction_zero_vertex (n : ℕ)
    (x : (_root_.SerrePositivity.EInfinity.BarrattEccles.complex A n).X 0) (b : Fin 2) :
    ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.barrattEcclesCoalgebra A).coaction n).f 0
      (ιTensorObj (_root_.SerrePositivity.EInfinity.BarrattEccles.complex A n) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.interval A) 0 0 0 rfl
        (x ⊗ₜ[A] _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.faceVector A (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.vertex b))) =
      (singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat A))).hom
        ((_root_.SerrePositivity.EInfinity.BarrattEccles.complexAugmentation A n).f 0 x) •
          _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.zeroTensor A (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.interval A) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.faceVector A (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.vertex b)) n := by
  change (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.cochainAction A n).f 0
    (((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.cochainMap A n) ▷ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.interval A).f 0
      (ιTensorObj (_root_.SerrePositivity.EInfinity.BarrattEccles.complex A n) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.interval A) 0 0 0 rfl
        (x ⊗ₜ[A] _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.faceVector A (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.vertex b)))) = _
  rw [SerrePositivity.DifferentialGraded.whiskerRight_apply,
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.cochainAction_zero_vertex, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.zeroAugmentation_cochainMap_zero]

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts
