module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.FiberwiseFunctorFamilies
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.IntervalShapeContraction
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.EquivalencePath

/-!
概要：底を固定した path の全空間の、定値 path への収縮。
方針：形状変数を収縮した評価を curry し、指定した同じ底射へ戻す。
規約：底射は全時刻で固定する。
使われ方：始点評価の底上のホモトピー逆と、全空間 Kan path 比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {E B : SSet.{u}} (p : E ⟶ B)
local notation "P" => fiberwiseFunctorSpace p Δ[1]
local notation "a" => pullback.fst (CategoryTheory.Functor.map (ihom Δ[1]) p)
  (constantDiagram Δ[1] B)

/-- 概要：定値底の path の形状収縮を全空間内で実現する射。
方針：元の評価の前に形状収縮を合成し、元と同じ底射で curry する。
規約：時刻は右因子。使われ方：始点評価の逆の変形。 -/
def fiberwiseIntervalContraction : P ⊗ (Δ[1] : SSet.{u}) ⟶ P :=
  fiberwiseFunctorCurry p (fst P Δ[1] ≫ fiberwiseFunctorProjection p Δ[1])
    (intervalShapeContraction P ≫ uncurry a) (by
      rw [Category.assoc, fiberwiseFunctorUncurry_projection, ← Category.assoc,
        intervalShapeContraction_projection, Category.assoc])

/-- 概要：収縮は底射を全時刻で固定する。
方針：族の指定底への射影式。
規約：元の底射。使われ方：底上のホモトピーの厳密な条件。 -/
lemma fiberwiseIntervalContraction_projection :
    fiberwiseIntervalContraction p ≫ fiberwiseFunctorProjection p Δ[1] =
      fst P Δ[1] ≫ fiberwiseFunctorProjection p Δ[1] :=
  fiberwiseFunctorCurry_projection _ _ _ _

/-- 概要：収縮の関手成分は形状収縮した元の評価。
方針：族の第一射影を計算する。
規約：全時刻の等式。使われ方：両端のホモトピーの検査。 -/
lemma fiberwiseIntervalContraction_fst :
    fiberwiseIntervalContraction p ≫ a = curry (intervalShapeContraction P ≫ uncurry a) :=
  fiberwiseFunctorCurry_fst _ _ _ _

/-- 概要：収縮の時刻零は始点評価の後の定値 path の切断。
方針：関手成分は形状収縮の零端、底成分は同じ底射として照合する。
規約：元の始点評価。使われ方：変形 retract の始端。 -/
lemma fiberwiseIntervalContraction_zero :
    SSet.ι₀ ≫ fiberwiseIntervalContraction p =
      fiberwiseIntervalEndpoint p 0 ≫ fiberwiseFunctorConstant p Δ[1] := by
  apply pullback.hom_ext (f := (ihom (Δ[1] : SSet.{u})).map p) (g := constantDiagram Δ[1] B)
  · simp only [Category.assoc, fiberwiseIntervalContraction_fst, fiberwiseFunctorConstant_fst]
    apply uncurry_injective
    rw [uncurry_natural_left, uncurry_curry, ← Category.assoc,
      intervalShapeContraction_zero, Category.assoc, ← curry_evaluateFunctorAt_interval,
      curry_uncurry, uncurry_comp_constantDiagram]
    rfl
  · change (SSet.ι₀ ≫ fiberwiseIntervalContraction p) ≫ fiberwiseFunctorProjection p Δ[1] =
      (fiberwiseIntervalEndpoint p 0 ≫ fiberwiseFunctorConstant p Δ[1]) ≫
        fiberwiseFunctorProjection p Δ[1]
    rw [Category.assoc, fiberwiseIntervalContraction_projection, ← Category.assoc]
    simp only [Category.assoc, fiberwiseFunctorConstant_projection,
      fiberwiseIntervalEndpoint_projection]
    rfl

/-- 概要：収縮の時刻一は元の path の恒等射。
方針：関手成分は形状収縮の一端、底成分は同じ底射として照合する。
規約：元の全空間の恒等射。使われ方：変形 retract の終端。 -/
lemma fiberwiseIntervalContraction_one :
    SSet.ι₁ ≫ fiberwiseIntervalContraction p = 𝟙 P := by
  apply pullback.hom_ext (f := (ihom (Δ[1] : SSet.{u})).map p) (g := constantDiagram Δ[1] B)
  · rw [Category.assoc, fiberwiseIntervalContraction_fst, Category.id_comp]
    apply uncurry_injective
    rw [uncurry_natural_left, uncurry_curry, ← Category.assoc,
      intervalShapeContraction_one, Category.id_comp]
  · change (SSet.ι₁ ≫ fiberwiseIntervalContraction p) ≫ fiberwiseFunctorProjection p Δ[1] =
      (𝟙 P) ≫ fiberwiseFunctorProjection p Δ[1]
    rw [Category.assoc, fiberwiseIntervalContraction_projection]
    rfl

end SerrePositivity.InfinityCategories.F2
