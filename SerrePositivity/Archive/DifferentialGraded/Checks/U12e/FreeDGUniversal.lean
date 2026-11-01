module
public import SerrePositivity.DifferentialGraded.Resolution.Free.Evaluation
public import Mathlib.Data.ZMod.Basic

/-! # 自由dg圏の結合則・K-flat Hom・厳密普遍性の監査

## 概要
自由dg圏の結合則・K-flat Hom・厳密普遍性の監査。

## 方針
既存の例・型照合・公理監査集合を保持し、証明済みの個別契約を検査する。

## 規約と注意
U12e-general（中断）の一部。R1〜R7への足場として保持する。収録された個別宣言の証明済み範囲と、一般経路全体の未受入を区別する。
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。対応する一般APIの再現可能な検査入口。中断した一般経路を再開する際にも同じ対象を再実行できる。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/
@[expose] public section
noncomputable section
universe u v w
open CategoryTheory
open SerrePositivity.DifferentialGraded
open SerrePositivity.DifferentialGraded.FreeDGCategory
variable (A : Type u) [CommRing A] (D : Type v) [Small.{u} D]
  (E : Type w) [DGCategory A E]

example (K : ComplexQuiver A D) : DGCategory A (Objects A D K) := inferInstance

example (K : ComplexQuiver A D) (hK : ∀ x y, complexKFlat A (K x y)) :
    localHomKFlat A (Objects A D K) := homKFlat A D K hK

example (K : ComplexQuiver A D) :
    DGFunctor A (Objects A D K) E ≃ GeneratorMap A D E K := universalEquiv A D E K

-- 対象写像と生成辺のchain mapだけからdg関手が一意に定まる。
example (K : ComplexQuiver A D) (g : GeneratorMap A D E K) :
    ∃! F : DGFunctor A (Objects A D K) E, restrict A D E K F = g := by
  refine ⟨extend A D E K g, restrict_extend A D E K g, ?_⟩
  intro F h
  exact extension_unique A D E K g F h

example (K : ComplexQuiver A D) (F : DGFunctor A (Objects A D K) E) :
    lift A D E K F.obj (fun x y => edgeInclusion A D K x y ≫ F.map x y) = F :=
  lift_reconstruction A D E K F

example (D : Type v) [Small.{0} D] (E : Type w) [DGCategory (ZMod 2) E]
    (K : ComplexQuiver (ZMod 2) D) :
    DGFunctor (ZMod 2) (Objects (ZMod 2) D K) E ≃ GeneratorMap (ZMod 2) D E K :=
  universalEquiv (ZMod 2) D E K

#print axioms SerrePositivity.DifferentialGraded.FreeDGCategory.appendPath
#print axioms SerrePositivity.DifferentialGraded.FreeDGCategory.appendPath_inclusion
#print axioms SerrePositivity.DifferentialGraded.FreeDGCategory.composition_left_inclusion
#print axioms SerrePositivity.DifferentialGraded.FreeDGCategory.appendWord
#print axioms SerrePositivity.DifferentialGraded.FreeDGCategory.edgePrefix
#print axioms SerrePositivity.DifferentialGraded.FreeDGCategory.edgePrefix_unit
#print axioms SerrePositivity.DifferentialGraded.FreeDGCategory.edgePrefix_nonempty
#print axioms SerrePositivity.DifferentialGraded.FreeDGCategory.appendPath_unit
#print axioms SerrePositivity.DifferentialGraded.FreeDGCategory.appendWord_cons
#print axioms SerrePositivity.DifferentialGraded.FreeDGCategory.appendPath_edgePrefix
#print axioms SerrePositivity.DifferentialGraded.FreeDGCategory.composition_edgePrefix
#print axioms SerrePositivity.DifferentialGraded.FreeDGCategory.appendWord_assoc
#print axioms SerrePositivity.DifferentialGraded.FreeDGCategory.appendPath_assoc
#print axioms SerrePositivity.DifferentialGraded.FreeDGCategory.composition_assoc
#print axioms SerrePositivity.DifferentialGraded.FreeDGCategory.Objects
#print axioms SerrePositivity.DifferentialGraded.FreeDGCategory.objectsSmall
#print axioms SerrePositivity.DifferentialGraded.FreeDGCategory.dgCategory
#print axioms SerrePositivity.DifferentialGraded.FreeDGCategory.homKFlat
#print axioms SerrePositivity.DifferentialGraded.FreeDGCategory.lift
#print axioms SerrePositivity.DifferentialGraded.FreeDGCategory.lift_edge
#print axioms SerrePositivity.DifferentialGraded.FreeDGCategory.composition_edge_path
#print axioms SerrePositivity.DifferentialGraded.FreeDGCategory.functor_word
#print axioms SerrePositivity.DifferentialGraded.FreeDGCategory.functor_path
#print axioms SerrePositivity.DifferentialGraded.FreeDGCategory.homEvaluation_reconstruction
#print axioms SerrePositivity.DifferentialGraded.FreeDGCategory.lift_reconstruction
#print axioms SerrePositivity.DifferentialGraded.FreeDGCategory.GeneratorMap
#print axioms SerrePositivity.DifferentialGraded.FreeDGCategory.restrict
#print axioms SerrePositivity.DifferentialGraded.FreeDGCategory.extend
#print axioms SerrePositivity.DifferentialGraded.FreeDGCategory.extend_restrict
#print axioms SerrePositivity.DifferentialGraded.FreeDGCategory.restrict_extend
#print axioms SerrePositivity.DifferentialGraded.FreeDGCategory.universalEquiv
#print axioms SerrePositivity.DifferentialGraded.FreeDGCategory.extension_unique
