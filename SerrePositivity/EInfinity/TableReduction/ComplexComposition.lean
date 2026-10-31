module

public import SerrePositivity.EInfinity.Surjection.ComplexComposition
public import SerrePositivity.EInfinity.BarrattEccles.ShuffleChainMap
public import SerrePositivity.HomologicalAlgebra.CochainTensor.Basic

/-!
# 整数複体の射としての TR の部分合成保存

概要：Berger–Fresse §1.3 の一般の TR が実際の複体の部分合成射を保つことを証明する。
方針：全テンソルの双次数成分を比較し、純粋テンソル上の整数双線形保存を使う。
規約：非有界整数複体・全 arity・全入力位置。
使われ方：TR オペラッド射の comp 保存条件。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity.TableReduction

open CategoryTheory MonoidalCategory HomologicalComplex
open SerrePositivity.DifferentialGraded

variable (A : Type u) [CommRing A]

/-- 概要：加群テンソルの各整数成分で TR は合成を保つ（BF §1.3）。
方針：純粋テンソルの外延性で双線形保存へ帰着する。
規約：次数の和の任意の等式。
使われ方：全テンソル複体の合成保存を組み立てる。 -/
lemma cochainCompositionComponent_comm (m n : ℕ) (i : Fin (m + 1))
    (r s t : ℤ) (h : r + s = t) :
    BarrattEccles.cochainShuffleComponent A m n i r s t h ≫ (cochainMap A (m + n)).f t =
      ((cochainMap A (m + 1)).f r ⊗ₘ (cochainMap A n).f s) ≫
        Surjection.cochainCompositionComponent A m n i r s t h := by
  apply ModuleCat.hom_ext
  apply TensorProduct.ext
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro y
  exact cochainMap_compositionBilinear A m n i r s t h x y

/-- 概要：整数複体の TR は実際の全ての部分合成射を保つ（BF §1.3）。
方針：双次数テンソル成分の直和の外延性と構成済みの成分保存を使う。
規約：arity 零を含む全演算。
使われ方：TR をオペラッド射へまとめるための合成条件。 -/
lemma complexPartialComposition_comm (m n : ℕ) (i : Fin (m + 1)) :
    BarrattEccles.partialComposition A m n i ≫ cochainMap A (m + n) =
      (cochainMap A (m + 1) ⊗ₘ cochainMap A n) ≫
        Surjection.complexPartialComposition A m n i := by
  apply tensorHom_ext
  intro r s t h
  simp only [HomologicalComplex.comp_f,
    BarrattEccles.ι_partialComposition_assoc, ι_tensorHom_assoc,
    Surjection.ι_complexPartialComposition]
  exact cochainCompositionComponent_comm A m n i r s t h

end SerrePositivity.EInfinity.TableReduction
