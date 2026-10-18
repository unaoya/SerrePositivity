module

public import SerrePositivity.KST.Comparison.DGAlgebra
public import Mathlib.Algebra.Homology.Embedding.TruncLEHomology

/-!
# connective な cochain 複体の非正切断

概要：正次数のホモロジーが消える複体では good truncation の包含は擬同型である。
方針：Mathlib の切断のホモロジー計算と非正次数の埋め込みを使う。
規約：SS03 の非負 chain 規約を cochain の H^i = 0 (i > 0) に読み替える。
使われ方：KST §2.2 の ΓA の入力の切断の正当化。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false

universe u

namespace SerrePositivity.KST.Comparison

open CategoryTheory DifferentialGraded HomologicalComplex

variable {R : Type u} [CommRing R]

/--
概要：正のホモロジーが零なら非正次数の像の外で完全である。
方針：埋め込みの像の外は正次数であり、homology の零性と完全性は同値。
規約：SS03 §2.1 の connective の cochain 表示。
使われ方：good truncation の擬同型性。
-/
theorem supported_nonpositive_of_connective (K : Complex R)
    (h : ∀ i : ℤ, 0 < i → Limits.IsZero (K.homology i)) :
    K.IsSupported (ComplexShape.embeddingUpIntLE 0) where
  exactAt i hi := by
    rw [exactAt_iff_isZero_homology]
    exact h i ((ComplexShape.notMem_range_embeddingUpIntLE_iff 0 i).mp hi)

/--
概要：connective な cochain 複体の非正 good truncation の包含は擬同型。
方針：非正次数での支持条件を Mathlib の切断のホモロジー定理に渡す。
規約：正次数の項が零という強い仮定は要求しない。SS03 §2.1 の読み替え。
使われ方：一般の connective dg 代数から Γ の入力を取ること。
-/
theorem quasiIso_connective_truncation (K : Complex R)
    (h : ∀ i : ℤ, 0 < i → Limits.IsZero (K.homology i)) :
    QuasiIso (K.ιTruncLE (ComplexShape.embeddingUpIntLE 0)) :=
  (K.quasiIso_ιTruncLE_iff_isSupported (ComplexShape.embeddingUpIntLE 0)).mpr
    (supported_nonpositive_of_connective K h)

/--
概要：connective dg 代数の underlying 複体の good truncation は擬同型である。
方針：一対象 dg 圏の Hom 複体に切断定理を適用する。
規約：乗法は Γ の標準成分模型で直接構成する。SS03 (2.9)。
使われ方：KST §2.2 の一般の connective 入力。
-/
theorem DGAlgebraModel.quasiIso_truncation (A : DGAlgebraModel R)
    (h : A.IsConnective R) :
    QuasiIso ((A.Hom PUnit.unit PUnit.unit).ιTruncLE (ComplexShape.embeddingUpIntLE 0)) :=
  quasiIso_connective_truncation _ h

end SerrePositivity.KST.Comparison
