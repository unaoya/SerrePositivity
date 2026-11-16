module

public import SerrePositivity.EInfinity.SimplexCuts.VectorTensorTransport
public import SerrePositivity.EInfinity.SimplexCuts.SignedTerms

/-!
# 元の切断テンソルの同じ次数の移送

Berger–Fresse §2.2.6、M14 L12a の既存構成の法則、報告 §299。
同じ生成元と斉次テンソルを、元の等式移送と同じ複体射で読む。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.SimplexCuts
open CategoryTheory MonoidalCategory HomologicalComplex
open SerrePositivity.DifferentialGraded SerrePositivity.TensorPowers
open scoped Simplicial
variable {A : Type u} [CommRing A]

/-- 等しい加群の移送は同じ元を保つ（BF §2.2.6の次数移送の補助）。 -/
lemma module_eqToHom_apply_heq (M N : ModuleCat A) (h : M = N) (x : M) :
    HEq ((eqToHom h).hom x) x := by
  subst N
  rfl

/-- 指定次数へ移しても、同じ斉次テンソルである（BF §2.2.6）。 -/
lemma vectorTensorAt_heq (K : Complex A) (r : ℕ)
    (f : Fin r → Σ d : ℕ, K.X (-(d : ℤ))) (t : ℤ)
    (ht : -(vectorDegree K r f : ℤ) = t) :
    HEq (vectorTensorAt K r f t ht) (vectorTensor K r f) :=
  module_eqToHom_apply_heq _ _ _ _

/-- 共通次数の切断テンソルは、元の同じ斉次純粋テンソル（BF §2.2.6）。 -/
lemma cutTensorAt_heq_vectorTensor (A : Type u) [CommRing A] (S : SSet.{0})
    {m q r : ℕ} (s : Cut m q) (w : Surjection.Word r (m + 1)) (x : S _⦋q⦌) :
    HEq (cutTensorAt A S s w x)
      (vectorTensor (chains A S) r (fun a =>
        ⟨outputDegree s w a, gen A S (outputDegree s w a) (S.map (face s w a).op x)⟩)) :=
  module_eqToHom_apply_heq _ _ _ _

end SerrePositivity.EInfinity.SimplexCuts
