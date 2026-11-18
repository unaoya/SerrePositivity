module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.CutTensor
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.TensorNaturality

/-!
模型。文献の定義との比較は後で
# 一般の切断テンソルの自然性

Berger–Fresse §2.2.6。切断の同じ面を保持し、単体集合の射を全出力へ移す。
L05 の符号付き切断項の自然性の、純粋テンソルの部分。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
open _root_.CategoryTheory
open _root_.SerrePositivity.TensorPowers
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A]

lemma cutTensor_map {m q r : ℕ} {S T : SSet.{0}} (f : S ⟶ T)
    (s : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut m q) (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Word r (m + 1)) (x : S _⦋q⦌) :
    (_root_.SerrePositivity.TensorPowers.map ((_root_.SerrePositivity.EInfinity.BarrattEccles.normalizedFunctor A).map f) r).f
      (-(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.degreeSum r (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.outputDegree s u) : ℤ)) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.cutTensor A S s u x) =
        _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.cutTensor A T s u (f.app _ x) := by
  unfold _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.cutTensor
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.tensorValue_map]
  congr 1
  funext a
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.gen_naturality]
  exact congrArg (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.gen A T (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.outputDegree s u a))
    (ConcreteCategory.congr_hom (f.naturality (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.face s u a).op) x)

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
