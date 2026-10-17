module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.SimplexMatchingTerminal
public import SerrePositivity.HomotopicalAlgebra.Simplicial.NerveCoherentFamily
public import SerrePositivity.HomotopicalAlgebra.Simplicial.SimplexLatchingBoundary

/-!
# 退化を可逆にする図式のmatching条件からReedy右クラスへの所属を導く

## 概要
退化を可逆にする図式のmatching条件からReedy右クラスへの所属を導く。
一般に再利用できる道具として分類Aに整理する。

## 方針（定義・証明）
圏の射列を各単体として評価し、自然変換や端点の射を明示する。
単体ごとの合成と端点の式を照合して、全体の写像を得る。

## 規約と注意
モデル構造と射クラスの一致を要求する入口では、その指定データを仮定する。
このファイルがHT-KQの引用モデルを自動的に選ぶとは解釈しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない（依存監査で確認済み）。
今後はK理論空間の充填・ホモトピー比較やπ_*計算の基礎として利用できる。
[棚卸し m0558][inventory]と[計画書 §396][plan]を参照。

[inventory]: ../../../formalization-plans/k-theory-generalization-inventory.md#m0558
[plan]: ../../../formalization-plans/k-theory.md
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Reedy right conditions for small diagrams inverting simplex degeneracies

Empty inverse boundaries are controlled by the actual object projection.
Nonempty inverse boundaries have a terminal core and give isomorphisms.
This proves the value-side Reedy condition, rather than assuming it.
-/

@[expose] public section
universe w v uD vD
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open SerrePositivity.Reedy

namespace SerrePositivity.SimplicialModel.SimplexInverseMatching
variable (X : SSet.{w}) (s : X.Elementsᵒᵖ)

abbrev point : X.Elementsᵒᵖ ⥤ SSet.{v} :=
  (Functor.const X.Elementsᵒᵖ).obj (SSet.stdSimplex.obj (SimplexCategory.mk 0))

def pointMatchingTerminal : IsTerminal ((matchingEvaluation (SimplexIndexFinite.reedy X) s).obj
    (point.{w, v} X)) :=
  IsTerminal.ofUniqueHom (fun Z => limit.lift
    (matchingTarget (SimplexIndexFinite.reedy X) s ⋙ point.{w, v} X)
    { pt := Z
      π := { app _ := SSet.stdSimplex.isTerminalObj₀.from Z
             naturality {_ _} _ := SSet.stdSimplex.isTerminalObj₀.hom_ext _ _ } })
    (fun _ _ => by
      apply limit.hom_ext
      intro q
      exact SSet.stdSimplex.isTerminalObj₀.hom_ext _ _)

def emptyMatchingTerminal (A : X.Elementsᵒᵖ ⥤ SSet.{v})
    [IsEmpty (SimplexMatchingTerminal.Index X s)] :
    IsTerminal ((matchingEvaluation (SimplexIndexFinite.reedy X) s).obj A) :=
  IsTerminal.ofUniqueHom (fun Z => limit.lift
    (matchingTarget (SimplexIndexFinite.reedy X) s ⋙ A)
    { pt := Z
      π := { app q := isEmptyElim q
             naturality {q} _ := isEmptyElim q } })
    (fun _ _ => by
      apply limit.hom_ext
      intro q
      exact isEmptyElim q)

variable [ModelCategory SSet.{v}]
  (A : X.Elementsᵒᵖ ⥤ SSet.{v}) (p : A ⟶ point.{w, v} X)
  (hA : ∀ {a b : X.Elementsᵒᵖ} (f : a ⟶ b),
    (elementsDirect (direct := simplexInverse.op) X).op f → IsIso (A.map f))
  (hp : ∀ s, trivialFibrations SSet.{v} (p.app s))

include hA hp in
lemma relativeMatching_trivialFibration :
    trivialFibrations SSet.{v} (relativeMatchingMap (SimplexIndexFinite.reedy X) s p) := by
  classical
  by_cases h : Nonempty (SimplexMatchingTerminal.Index X s)
  · have : Nonempty (SimplexMatchingTerminal.Index X s) := h
    have : IsIso ((matchingComparison (SimplexIndexFinite.reedy X) s).app A) :=
      SimplexMatchingTerminal.matchingComparison_isIso X s A hA
    have : IsIso ((matchingComparison (SimplexIndexFinite.reedy X) s).app (point.{w, v} X)) :=
      isIso_of_isTerminal SSet.stdSimplex.isTerminalObj₀ (pointMatchingTerminal X s) _
    have hi : Arrow.mk (relativeMatchingMap (SimplexIndexFinite.reedy X) s p) ≅
        Arrow.mk ((matchingComparison (SimplexIndexFinite.reedy X) s).app A) :=
      Arrow.isoMk (Iso.refl _)
      (asIso (pullback.snd
        ((matchingComparison (SimplexIndexFinite.reedy X) s).app (point.{w, v} X))
        ((matchingEvaluation (SimplexIndexFinite.reedy X) s).map p))) (by
          change (𝟙 _) ≫ _ = pullback.lift _ _ _ ≫ pullback.snd _ _
          rw [Category.id_comp, pullback.lift_snd]
          rfl)
    apply ((trivialFibrations SSet.{v}).arrow_iso_iff hi).mpr
    change trivialFibrations SSet.{v}
      ((matchingComparison (SimplexIndexFinite.reedy X) s).app A)
    exact (trivialFibrations SSet.{v}).of_isIso _
  · have : IsEmpty (SimplexMatchingTerminal.Index X s) := not_nonempty_iff.mp h
    have : IsIso ((matchingEvaluation (SimplexIndexFinite.reedy X) s).map p) :=
      isIso_of_isTerminal (emptyMatchingTerminal X s A) (pointMatchingTerminal X s) _
    have hi : Arrow.mk (relativeMatchingMap (SimplexIndexFinite.reedy X) s p) ≅
        Arrow.mk (p.app s) := Arrow.isoMk (Iso.refl _)
      (asIso (pullback.fst
        ((matchingComparison (SimplexIndexFinite.reedy X) s).app (point.{w, v} X))
        ((matchingEvaluation (SimplexIndexFinite.reedy X) s).map p))) (by
          change (𝟙 _) ≫ _ = pullback.lift _ _ _ ≫ pullback.fst _ _
          rw [Category.id_comp, pullback.lift_fst]
          rfl)
    apply ((trivialFibrations SSet.{v}).arrow_iso_iff hi).mpr
    change trivialFibrations SSet.{v} (p.app s)
    exact hp s

include hA hp in
/-- 退化を可逆にする図式のmatching条件からReedy右クラスへの所属を導く。

モデル構造と射クラスの一致を要求する入口では、その指定データを仮定する。
圏の射列を各単体として評価し、自然変換や端点の射を明示する。
単体ごとの合成と端点の式を照合して、全体の写像を得る。
-/
lemma reedyRight : Reedy.reedyRight (SimplexIndexFinite.reedy X)
    (trivialFibrations SSet.{v}) p := fun s => relativeMatching_trivialFibration X s A p hA hp

end SerrePositivity.SimplicialModel.SimplexInverseMatching
