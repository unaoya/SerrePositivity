module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.CochainDegrees
public import SerrePositivity.HomologicalAlgebra.CochainTensor.Basic
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Category.ModuleCat.EpiMono

/-!
模型。文献の定義との比較は後で
# 整数 TR とテンソル積の全射消去

概要：Berger–Fresse §1.3 の全射 TR で χ の複体射の法則を判定する消去界面を用意する。
方針：加群の各成分の全射性とテンソルの純粋元による生成を使う。
規約：テンソルの因子や始域に cofibrancy・平坦性を追加しない。
使われ方：TR の成分とその二重・三重テンソルを前合成してオペラッド法則を移す。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory _root_.HomologicalComplex
open _root_.SerrePositivity.DifferentialGraded

variable (A : Type u) [CommRing A]

/-- 概要：整数 TR は複体の圏で全射（BF §1.3.4）。
方針：全整数次数での加群の全射性から複体射の epi を得る。
規約：任意の可換環と全 arity。
使われ方：TR の前合成による複体射の等式判定。 -/
lemma cochainMap_epi (n : ℕ) : Epi (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.cochainMap A n) := by
  apply HomologicalComplex.epi_of_epi_f
  intro r
  exact (ModuleCat.epi_iff_surjective _).mpr (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.cochainMap_f_surjective_int A n r)

/-- 概要：整数加群複体の二つの全射のテンソルは全射（BF §1.3 の法則移送に使用）。
方針：各斉次純粋テンソルの二因子の逆像で後続射の一致を判定する。
規約：複体の射の全射性だけを使い、平坦性を仮定しない。
使われ方：全射 TR の任意の括弧のテンソルによる消去。 -/
lemma tensor_epi_of_epi {P P' Q Q' : Complex A} (f : P ⟶ P') (g : Q ⟶ Q')
    [Epi f] [Epi g] : Epi (f ⊗ₘ g) := by
  constructor
  intro T a b h
  apply tensorHom_ext
  intro r s t ht
  apply ModuleCat.hom_ext
  apply TensorProduct.ext
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro y
  obtain ⟨x, rfl⟩ := (ModuleCat.epi_iff_surjective (f.f r)).mp inferInstance x
  obtain ⟨y, rfl⟩ := (ModuleCat.epi_iff_surjective (g.f s)).mp inferInstance y
  have hh := congrArg (fun z => ιTensorObj P Q r s t ht ≫ z.f t) h
  simp only [HomologicalComplex.comp_f, ι_tensorHom_assoc] at hh
  exact congrArg (fun z => z (x ⊗ₜ[A] y)) hh

/-- 概要：二つの arity の TR のテンソルは全射（BF §1.3.4）。
方針：構成済みの TR の全射性とテンソル全射性を局所的に使う。
規約：モデル構造や全射性の global instance を追加しない。
使われ方：χ の内外同変性と部分合成の等式を BE へ戻す。 -/
lemma tensor_cochainMap_epi (m n : ℕ) : Epi (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.cochainMap A m ⊗ₘ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.cochainMap A n) := by
  let _ : Epi (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.cochainMap A m) := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.cochainMap_epi A m
  let _ : Epi (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.cochainMap A n) := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.cochainMap_epi A n
  exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.tensor_epi_of_epi A _ _

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction
