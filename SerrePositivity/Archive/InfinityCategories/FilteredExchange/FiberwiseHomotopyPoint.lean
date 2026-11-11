module

public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FiberwiseFunctorSpace
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.IntervalReplacementPath

/-!
概要：底を全時刻で固定する指定円柱を fiberwise interval family の実際の射にする。
方針：円柱を curry し、底の固定条件で相対内部 Hom の引き戻しへ入れる。
規約：元の全円柱を保持。使われ方：coherent 錐から全空間 interval 引き戻しへの比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {A E B : SSet.{u}} (p : E ⟶ B) (a : A ⟶ B) {f g : A ⟶ E}
  (H : SSet.Homotopy f g)
  (hB : H.h ≫ p = fst A (Δ[1] : SSet.{u}) ≫ a)

/-- 概要：元の底固定円柱を fiberwise interval family へ入れる。
方針：元の円柱の curry と底射を引き戻しへ入れる。
規約：全円柱を保持。使われ方：元の二三角形から全空間模型への比較。 -/
def fiberwiseHomotopyPoint : A ⟶ fiberwiseFunctorSpace p (Δ[1] : SSet.{u}) :=
  pullback.lift (curry ((β_ (Δ[1] : SSet.{u}) A).hom ≫ H.h)) a (by
    apply uncurry_injective
    rw [uncurry_natural_right, uncurry_curry, uncurry_comp_constantDiagram,
      Category.assoc, hB]
    rfl)

/-- 概要：構成した射の全 path 座標は元の指定円柱。
方針：第一射影。規約：厳密な等式。使われ方：全 path の照合。 -/
lemma fiberwiseHomotopyPoint_path :
    fiberwiseHomotopyPoint p a H hB ≫
      pullback.fst ((ihom (Δ[1] : SSet.{u})).map p) (constantDiagram Δ[1] B) =
        curry ((β_ (Δ[1] : SSet.{u}) A).hom ≫ H.h) := pullback.lift_fst _ _ _

/-- 概要：構成した射は元の底射を厳密に保つ。
方針：第二射影。規約：元の a。使われ方：底上の全空間比較。 -/
lemma fiberwiseHomotopyPoint_projection :
    fiberwiseHomotopyPoint p a H hB ≫ fiberwiseFunctorProjection p Δ[1] = a :=
  pullback.lift_snd _ _ _

/-- 概要：元の始点射を回収。
方針：元の全 path の始点評価。規約：厳密な等式。使われ方：第一脚の持ち上げ条件。 -/
lemma fiberwiseHomotopyPoint_zero :
    fiberwiseHomotopyPoint p a H hB ≫ fiberwiseIntervalEndpoint p 0 = f := by
  rw [fiberwiseIntervalEndpoint, ← Category.assoc, fiberwiseHomotopyPoint_path]
  change curry _ ≫ evaluateFunctorAt (stdSimplex.obj₀Equiv.symm 0) = f
  rw [curry_evaluateFunctorAt_interval]
  exact H.h₀

/-- 概要：元の終点射を回収。
方針：元の全 path の終点評価。規約：厳密な等式。使われ方：第二脚の持ち上げ条件。 -/
lemma fiberwiseHomotopyPoint_one :
    fiberwiseHomotopyPoint p a H hB ≫ fiberwiseIntervalEndpoint p 1 = g := by
  rw [fiberwiseIntervalEndpoint, ← Category.assoc, fiberwiseHomotopyPoint_path]
  change curry _ ≫ evaluateFunctorAt (stdSimplex.obj₀Equiv.symm 1) = g
  rw [curry_evaluateFunctorAt_interval]
  exact H.h₁

end SerrePositivity.InfinityCategories.F2
