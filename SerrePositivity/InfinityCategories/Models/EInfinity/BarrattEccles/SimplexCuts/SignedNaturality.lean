module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.SignedTerms
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.CutNaturality

/-!
模型。文献の定義との比較は後で
# 符号付き切断項の自然性

Berger–Fresse §2.2.6。BF の符号と、全出力次数の指定した移送を保持して自然性を示す。
5a-5a L05。前提計算は正規化生成元・純粋テンソル・次数移送の三本。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
open _root_.CategoryTheory
open _root_.SerrePositivity.DifferentialGraded _root_.SerrePositivity.TensorPowers
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A]

/-- L05 の前提計算3：既存の複体射の成分は同じ次数等式の移送と両立する。 -/
lemma component_index_naturality {K L : Complex A} (f : K ⟶ L) {i j : ℤ} (h : i = j)
    (x : K.X i) :
    f.f j ((eqToHom (congrArg K.X h)).hom x) =
      (eqToHom (congrArg L.X h)).hom (f.f i x) := by
  subst j
  rfl

lemma cutTerm_map {m q r : ℕ} {S T : SSet.{0}} (f : S ⟶ T)
    (s : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut m q) (u : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Word r (m + 1)) (x : S _⦋q⦌) :
    (_root_.SerrePositivity.TensorPowers.map ((_root_.SerrePositivity.EInfinity.BarrattEccles.normalizedFunctor A).map f) r).f
      (-((m + q + 1 - r : ℕ) : ℤ)) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.cutTerm A S s u x) =
        _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.cutTerm A T s u (f.app _ x) := by
  unfold _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.cutTerm
  rw [map_zsmul]
  congr 1
  unfold _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.cutTensorAt
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.component_index_naturality, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.cutTensor_map]
  exact congrArg (fun t : ℕ => -(t : ℤ))
    ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.degreeSum_eq_sum r (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.outputDegree s u)).trans (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.outputDegree_sum s u))

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
