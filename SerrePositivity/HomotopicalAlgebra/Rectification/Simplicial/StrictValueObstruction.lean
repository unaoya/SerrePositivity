module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.ModelCompatibility
public import Mathlib.AlgebraicTopology.ModelCategory.Basic

/-!
# 中断した任意モデル源への一般化：StrictValueObstruction

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：Weakly equivalent Kan values can obstruct a strict functor on those fixed values。

## 方針（定義・証明）
整合図式の値変更による厳密化と宇宙縮小の問題に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0581][inventory]を参照する。

[inventory]: ../../../../formalization-plans/k-theory-generalization-inventory.md#m0581
[plan]: ../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Weakly equivalent Kan values can obstruct a strict functor on those fixed values

A cofibration/trivial-fibration factorization supplies a contractible Kan
complex with two distinct vertices. Thus it is not isomorphic to a point.
This obstructs preserving independently selected values when strictifying
a diagram over an isomorphism. It does not obstruct replacing its values.
-/

@[expose] public section
universe v
noncomputable section
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra

namespace SerrePositivity.SimplicialModel.StrictValueObstruction
variable [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)

abbrev point : SSet.{v} := SSet.stdSimplex.obj (SimplexCategory.mk 0)
abbrev interval : SSet.{v} := SSet.stdSimplex.obj (SimplexCategory.mk 1)
abbrev factorization := MorphismProperty.factorizationData
  (cofibrations SSet.{v}) (trivialFibrations SSet.{v})
  (SSet.stdSimplex.isTerminalObj₀.from interval)
abbrev complex : SSet.{v} := factorization.Z
abbrev toPoint : complex ⟶ point := factorization.p
abbrev fromInterval : interval ⟶ complex := factorization.i

include hcof in
lemma fromInterval_mono : Mono (fromInterval.{v}) := by
  exact (congrArg (fun W : MorphismProperty SSet.{v} => W fromInterval) hcof).mp
    factorization.hi

lemma toPoint_trivialFibration : trivialFibrations SSet.{v} toPoint := factorization.hp

omit [ModelCategory SSet.{v}] in
lemma point_kanComplex : SSet.KanComplex (point.{v}) := by
  have : IsIso (terminal.from (point.{v})) :=
    isIso_of_isTerminal SSet.stdSimplex.isTerminalObj₀ terminalIsTerminal _
  infer_instance

include hfib in
lemma complex_kanComplex : SSet.KanComplex (complex.{v}) := by
  have : Fibration toPoint.{v} := ⟨toPoint_trivialFibration.1⟩
  have : IsFibrant complex.{v} :=
    (isFibrant_iff_of_isTerminal toPoint SSet.stdSimplex.isTerminalObj₀).mpr inferInstance
  apply (SSet.modelCategoryQuillen.fibration_iff _).mpr
  rw [← hfib]
  exact mem_fibrations (terminal.from complex.{v})

include hcof in
lemma complex_not_subsingleton_vertices :
    ¬ Subsingleton ((complex.{v}).obj (Opposite.op (SimplexCategory.mk 0))) := by
  intro h
  have : Mono (fromInterval.{v}) := fromInterval_mono hcof
  have hinj := (CategoryTheory.mono_iff_injective
    ((fromInterval.{v}).app (Opposite.op (SimplexCategory.mk 0)))).mp inferInstance
  have he := hinj (h.elim
    ((fromInterval.{v}).app _ (SSet.stdSimplex.obj₀Equiv.symm 0))
    ((fromInterval.{v}).app _ (SSet.stdSimplex.obj₀Equiv.symm 1)))
  have : (0 : Fin 2) = 1 := congrArg SSet.stdSimplex.obj₀Equiv he
  exact Fin.zero_ne_one this

include hcof in
lemma not_iso_point : ¬ Nonempty (complex.{v} ≅ point) := by
  rintro ⟨e⟩
  apply complex_not_subsingleton_vertices hcof
  constructor
  intro x y
  apply (CategoryTheory.mono_iff_injective (e.hom.app _)).mp inferInstance
  apply SSet.stdSimplex.obj₀Equiv.injective
  apply Fin.ext
  omega

end SerrePositivity.SimplicialModel.StrictValueObstruction
