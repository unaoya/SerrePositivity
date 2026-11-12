module
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.PushoutShape

/-! # 中間頂点を動かす三角柱の三単体への写像

概要：三角形の両端を固定し、中間頂点だけを一つ進める三角柱を標準三単体に写す。
方針：頂点 (i,p) を 0、1+p、3 に送る単調写像を各単体に適用する。
規約：始端は面 2、終端は面 1。使われ方：D7 の中間対象の因子分解のホモトピー。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories
open CategoryTheory MonoidalCategory Opposite
open scoped _root_.Simplicial

/-- 三角柱の中間頂点だけを動かす単調写像。 -/
def triangleMiddlePrismOrder : (Fin 3 × Fin 2) →o Fin 4 where
  toFun x := ![0, x.2.castSucc.succ, 3] x.1
  monotone' := by decide

/-- 中間頂点の変更を表す三角柱から三単体への写像。 -/
def triangleMiddlePrism : (Δ[2] ⊗ Δ[1] : SSet.{u}) ⟶ Δ[3] where
  app _ := ↾fun s => SSet.stdSimplex.objEquiv.symm (SimplexCategory.Hom.mk {
    toFun i := triangleMiddlePrismOrder
      ((SSet.stdSimplex.objEquiv s.1).toOrderHom i, (SSet.stdSimplex.objEquiv s.2).toOrderHom i)
    monotone' := fun _ _ h => triangleMiddlePrismOrder.monotone
      ⟨(SSet.stdSimplex.objEquiv s.1).toOrderHom.monotone h,
        (SSet.stdSimplex.objEquiv s.2).toOrderHom.monotone h⟩ })
  naturality _ _ _ := by ext s; rfl

/-- 始端は中間の後の頂点を飛ばす面 2。 -/
lemma triangleMiddlePrism_zero :
    SSet.ι₀ ≫ triangleMiddlePrism.{u} = SSet.stdSimplex.δ (2 : Fin 4) := by
  ext n s
  apply SSet.stdSimplex.objEquiv.injective
  ext i
  change (triangleMiddlePrismOrder ((SSet.stdSimplex.objEquiv s).toOrderHom i, 0)).val =
    ((2 : Fin 4).succAbove ((SSet.stdSimplex.objEquiv s).toOrderHom i)).val
  generalize (SSet.stdSimplex.objEquiv s).toOrderHom i = j
  fin_cases j <;> rfl

/-- 終端は中間の元の頂点を飛ばす面 1。 -/
lemma triangleMiddlePrism_one :
    SSet.ι₁ ≫ triangleMiddlePrism.{u} = SSet.stdSimplex.δ (1 : Fin 4) := by
  ext n s
  apply SSet.stdSimplex.objEquiv.injective
  ext i
  change (triangleMiddlePrismOrder ((SSet.stdSimplex.objEquiv s).toOrderHom i, 1)).val =
    ((1 : Fin 4).succAbove ((SSet.stdSimplex.objEquiv s).toOrderHom i)).val
  generalize (SSet.stdSimplex.objEquiv s).toOrderHom i = j
  fin_cases j <;> rfl

/-- 対角上では三角柱の相によらず元の対角を保つ。 -/
lemma triangleMiddlePrism_diagonal :
    ((SSet.stdSimplex.δ (1 : Fin 3)) ▷ (Δ[1] : SSet.{u})) ≫ triangleMiddlePrism =
      CartesianMonoidalCategory.fst (Δ[1] : SSet.{u}) Δ[1] ≫
        SSet.stdSimplex.δ (1 : Fin 3) ≫ SSet.stdSimplex.δ (2 : Fin 4) := by
  ext n s
  apply SSet.stdSimplex.objEquiv.injective
  ext i
  change (triangleMiddlePrismOrder
      ((1 : Fin 3).succAbove ((SSet.stdSimplex.objEquiv s.1).toOrderHom i),
        (SSet.stdSimplex.objEquiv s.2).toOrderHom i)).val =
    ((2 : Fin 4).succAbove
      ((1 : Fin 3).succAbove ((SSet.stdSimplex.objEquiv s.1).toOrderHom i))).val
  generalize (SSet.stdSimplex.objEquiv s.1).toOrderHom i = j
  generalize (SSet.stdSimplex.objEquiv s.2).toOrderHom i = k
  fin_cases j <;> fin_cases k <;> rfl

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
