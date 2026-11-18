module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.VectorTensorTransport
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.SignedTerms

/-!
模型。文献の定義との比較は後で
# 元の切断テンソルの同じ次数の移送

Berger–Fresse §2.2.6、M14 L12a の既存構成の法則、報告 §299。
同じ生成元と斉次テンソルを、元の等式移送と同じ複体射で読む。
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

/-- 等しい加群の移送は同じ元を保つ（BF §2.2.6の次数移送の補助）。 -/
lemma module_eqToHom_apply_heq (M N : ModuleCat A) (h : M = N) (x : M) :
    HEq ((eqToHom h).hom x) x := by
  subst N
  rfl

/-- 指定次数へ移しても、同じ斉次テンソルである（BF §2.2.6）。 -/
lemma vectorTensorAt_heq (K : Complex A) (r : ℕ)
    (f : Fin r → Σ d : ℕ, K.X (-(d : ℤ))) (t : ℤ)
    (ht : -(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vectorDegree K r f : ℤ) = t) :
    HEq (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vectorTensorAt K r f t ht) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vectorTensor K r f) :=
  _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.module_eqToHom_apply_heq _ _ _ _

/-- 共通次数の切断テンソルは、元の同じ斉次純粋テンソル（BF §2.2.6）。 -/
lemma cutTensorAt_heq_vectorTensor (A : Type u) [CommRing A] (S : SSet.{0})
    {m q r : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut m q) (w : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Word r (m + 1)) (x : S _⦋q⦌) :
    HEq (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.cutTensorAt A S s w x)
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.vectorTensor (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.chains A S) r (fun a =>
        ⟨_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.outputDegree s w a, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.gen A S (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.outputDegree s w a) (S.map (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.face s w a).op x)⟩)) :=
  _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.module_eqToHom_apply_heq _ _ _ _

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
