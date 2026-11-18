module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.VectorTensorTransport

/-!
模型。文献の定義との比較は後で
# 元の斉次テンソルの全次数の移送

Berger–Fresse §2.2.6、M14 L12a の既存構成の法則、報告 §315。
同じ総次数・実際の複体射の値・全有限添字を保つ。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory _root_.HomologicalComplex
open _root_.SerrePositivity.DifferentialGraded _root_.SerrePositivity.TensorPowers
open scoped _root_.Simplicial
variable {A : Type u} [CommRing A]

/-- 同じ全次数への移送は、元のvectorTensorAtと可換（BF §2.2.6）。 -/
lemma vectorTensorAt_target_transport (K : Complex A) (n : ℕ)
    (f : Fin n → Σ d : ℕ, K.X (-(d : ℤ))) (t u : ℤ)
    (ht : -(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vectorDegree K n f : ℤ) = t) (hu : -(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vectorDegree K n f : ℤ) = u)
    (htu : t = u) :
    (eqToHom (congrArg (fun z : ℤ => (power K n).X z) htu)).hom
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vectorTensorAt K n f t ht) = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vectorTensorAt K n f u hu := by
  subst htu
  rfl

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
