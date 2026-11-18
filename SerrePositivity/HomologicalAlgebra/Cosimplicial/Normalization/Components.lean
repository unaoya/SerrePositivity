module

public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
public import Mathlib.Algebra.Category.ModuleCat.Basic

/-!
# 正規化余単体的加群の元の核と交代余面和

Dold–Kanの正規化とBerger–Fresse §2.2、M14 L19、報告 §395。
次数零は全体、正次数は元の全codegeneracyの核の共通部分とする。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.CosimplicialNormalization
open _root_.CategoryTheory
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A] (X : CosimplicialObject (ModuleCat.{u} A))

/-- 元の全codegeneracyの核による正規化部分（Dold–Kan、BF §2.2）。 -/
def normalizedSubmodule : (q : ℕ) → Submodule A (X.obj ⦋q⦌)
  | 0 => ⊤
  | q + 1 => ⨅ i : Fin (q + 1), LinearMap.ker (X.σ i).hom

/-- 元の交代余面の整数符号付き和（Dold–Kan、BF §2.2）。 -/
def alternatingCofaces (q : ℕ) : X.obj ⦋q⦌ →ₗ[A] X.obj ⦋q + 1⦌ :=
  ∑ i : Fin (q + 2), (-1 : ℤ) ^ (i : ℕ) • (X.δ i).hom

/-- 正次数の正規化条件は同じ全σ_iでの零（Dold–Kan、BF §2.2）。 -/
lemma mem_normalized_succ (q : ℕ) (a : X.obj ⦋q + 1⦌) :
    a ∈ _root_.SerrePositivity.CosimplicialNormalization.normalizedSubmodule A X (q + 1) ↔ ∀ i : Fin (q + 1), (X.σ i) a = 0 := by
  simp [_root_.SerrePositivity.CosimplicialNormalization.normalizedSubmodule, Submodule.mem_iInf, LinearMap.mem_ker]

end SerrePositivity.CosimplicialNormalization
