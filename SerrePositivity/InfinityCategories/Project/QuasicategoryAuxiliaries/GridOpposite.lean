module
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.PrismOpposite
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.PastingShapes

/-! # 標準格子の反転

概要：二つの標準単体の直積を両座標で反転し、長方形の面との両立を示す。
方針：標準単体の反転同型を直積に適用し、各次数の有限順序写像を計算する。
規約：値域も反転する。長方形の左と右は交換され、外側は保たれる。
使われ方：引き戻しの貼り合わせを押し出しの貼り合わせへ移す。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries

/-- 概要：標準格子の両座標と値域を反転する。
方針：各因子の反転同型の逆と直積の反転同型で前合成する。
規約：横 m、縦 n。使われ方：正方形と長方形の双対化。 -/
def reverseGrid {X : SSet.{u}} {m n : ℕ}
    (F : (Δ[m] : SSet.{u}) ⊗ Δ[n] ⟶ X) :
    (Δ[m] : SSet.{u}) ⊗ Δ[n] ⟶ X.op :=
  (((stdSimplex.opIso ⦋m⦌).inv ▷ Δ[n]) ≫
    ((Δ[m] : SSet.{u}).op ◁ (stdSimplex.opIso ⦋n⦌).inv)) ≫
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.opTensorIso Δ[m] Δ[n]).hom ≫ SSet.opFunctor.map F

/-- 概要：格子の反転は値域への後合成と可換。
方針：反転関手の合成保存を成分ごとに用いる。
規約：値域の射は任意。使われ方：反転四角形の輸送。 -/
lemma reverseGrid_postcomp {X Y : SSet.{u}} {m n : ℕ}
    (F : (Δ[m] : SSet.{u}) ⊗ Δ[n] ⟶ X) (p : X ⟶ Y) :
    reverseGrid (F ≫ p) = reverseGrid F ≫ SSet.opFunctor.map p := rfl

/-- 概要：格子を二度反転すると元の図式へ戻る。
方針：添字と値の二重反転を計算する。
規約：標的の二重反転同型を挿入する。使われ方：双対化の反映方向。 -/
lemma reverseGrid_double {X : SSet.{u}} {m n : ℕ}
    (F : (Δ[m] : SSet.{u}) ⊗ Δ[n] ⟶ X) :
    reverseGrid (reverseGrid F) ≫ (SSet.opFunctorCompOpFunctorIso.app X).hom = F := by
  apply SSet.hom_ext
  rintro ⟨⟨d⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨s, t⟩
  change F.app _ (_, _) = F.app _ (s, t)
  congr 2
  · apply stdSimplex.ext
    intro i
    change ((s i.rev.rev).rev).rev = s i
    simp
  · apply stdSimplex.ext
    intro i
    change ((t i.rev.rev).rev).rev = t i
    simp

/-- 概要：反転した長方形の面は、反対側の面の反転に一致する。
方針：余面の添字の反転と有限頂点の写像を計算する。
規約：余面 2 と 0 を交換し、1 を保つ。使われ方：引き戻しの貼り合わせ。 -/
lemma reverseGrid_pastingSquare {X : SSet.{u}}
    (F : (Δ[2] : SSet.{u}) ⊗ Δ[1] ⟶ X) (i : Fin 3) :
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare (reverseGrid F) i = reverseGrid (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare F i.rev) := by
  apply SSet.hom_ext
  rintro ⟨⟨d⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨s, t⟩
  change SSet.opObjEquiv.symm (F.app _ (_, _)) =
    SSet.opObjEquiv.symm (F.app _ (_, _))
  congr 2
  apply Prod.ext
  · apply stdSimplex.ext
    intro j
    change ((SimplexCategory.δ i).toOrderHom (s j.rev)).rev =
      (SimplexCategory.δ i.rev).toOrderHom ((s j.rev).rev)
    have h : ∀ (a : Fin 3) (b : Fin 2),
        ((SimplexCategory.δ a).toOrderHom b).rev =
          (SimplexCategory.δ a.rev).toOrderHom b.rev := by decide
    exact h i (s j.rev)
  · rfl

end SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries
