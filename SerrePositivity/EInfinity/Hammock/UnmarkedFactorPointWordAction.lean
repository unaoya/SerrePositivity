module

public import SerrePositivity.EInfinity.Hammock.UnmarkedFactorPointIndex
public import SerrePositivity.EInfinity.Hammock.UnmarkedFactorColimitImages

/-!
# 元の切断点と全語の作用

概要：圧縮・恒等列の挿入の前後で、依存和の実際の切断点が等しいことを証明する。
方針：像の最小列での因子の標準射の比較と元の最小列の回収を結合する。
規約：指定 prefix の実際の W-hammock と残りの元の余極限を使う。
使われ方：切断の全語の自然な余錐と余極限への降下。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.FirstFactor
open CategoryTheory

variable {C : Type u} [Category.{v} C] (W : MorphismProperty C)
  {a b : Word} {X Y : Paths C} {n : SimplexCategoryᵒᵖ}
  (f : a ⟶ b) (τ : (graph W.paths a X Y).obj n) (h : ∃ j, column W (τ.obj 0) j ≠ [])
  (hf : ∃ j, column W ((τ ⋙ WordAction.functor f).obj 0) j ≠ [])

lemma point_wordAction : point W τ h = point W (τ ⋙ WordAction.functor f) hf := by
  let i := AttachedPrefix.index W τ h
  have hi := column_wordAction_nonempty W f (τ.obj 0) i (AttachedPrefix.nonempty W τ h)
  calc
    point W τ h = pointAt W (τ ⋙ WordAction.functor f) (f.orderHom i) hi
        (FirstFactorAction.imagePrefix_arrow_mem W f τ h hi) := by
      apply FactorTarget.point_ext W (FirstFactorAction.generator_eq W f τ h hi).symm
      · exact FirstFactorAction.marked_prefix_colimit_image W f τ h hi
      · exact FirstFactorAction.residual_colimit_image W f τ h hi
    _ = point W (τ ⋙ WordAction.functor f) hf :=
      pointAt_eq W _ _ hi _ hf (firstColumn_wordAction W f (τ.obj 0) h hf).symm

end SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.FirstFactor
