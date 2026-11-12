module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.TransportTriangleParameter
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.FunctorNaturalityTriangles

/-!
概要：右の終点を潰す四角形の折り畳みと零番三角形への戻しを計算する。
方針：二時刻の第二成分を最大値へ送る同じ単調写像を使う。
規約：全係数を保持。使われ方：元の slice 四角形全体の回収。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 二つの時間の最大値。 -/
def squareUpperMaximum : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ Δ[1] :=
  stdSimplexProductMap ⟨fun x => max x.1 x.2, fun _ _ h => max_le_max h.1 h.2⟩

/-- 第一時間を保ち、第二時間を二時刻の最大値にする同じ係数の射。 -/
def squareUpperRetraction (P : SSet.{u}) :
    (Δ[1] : SSet.{u}) ⊗ (Δ[1] ⊗ P) ⟶ Δ[1] ⊗ (Δ[1] ⊗ P) :=
  lift (fst _ _) (lift
    (lift (fst _ _) (snd _ _ ≫ fst _ _) ≫ squareUpperMaximum) (snd _ _ ≫ snd _ _))

/-- 三角形へ畳んで元の零番三角形へ戻すと、同じ最大値の射になる。 -/
lemma transportTriangleParameter_triangle (P : SSet.{u}) :
    transportTriangleParameter P ≫ (squareTriangle 0 ▷ P) ≫
        (α_ (Δ[1] : SSet.{u}) Δ[1] P).hom = squareUpperRetraction P := by
  have htri : squareTriangle.{u} 0 =
      lift (stdSimplex.σ (0 : Fin 2)) (stdSimplex.σ (1 : Fin 2)) := by
    apply SSet.yonedaEquiv.injective
    apply Prod.ext <;> decide
  rw [htri]
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨s, t, p⟩
  apply Prod.ext
  · apply stdSimplex.ext
    intro i
    change (0 : Fin 2).predAbove (if s i = 0 then (t i).castSucc else 2) = s i
    generalize s i = a
    generalize t i = b
    fin_cases a <;> fin_cases b <;> rfl
  · apply Prod.ext
    · apply stdSimplex.ext
      intro i
      change (1 : Fin 2).predAbove (if s i = 0 then (t i).castSucc else 2) = max (s i) (t i)
      generalize s i = a
      generalize t i = b
      fin_cases a <;> fin_cases b <;> rfl
    · rfl

end SerrePositivity.InfinityCategories.F2
