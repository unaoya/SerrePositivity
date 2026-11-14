module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Homotopies.ComplexHomotopies.ComplexSquareMiddleData
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SquarePrismGluing

/-! # 中間対象変更の正方形全体のホモトピー

概要：右下の頂点を因子分解に沿って動かす正方形全体の比較を構成する。
方針：下三角形の中間対象比較と上三角形の定値ホモトピーを対角で貼る。
規約：始点・終点・上三角形を固定する。使われ方：D7 の標準 cofiber の接続射。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency true
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory MonoidalCategory DifferentialGraded
open scoped _root_.Simplicial
variable {S : Type u} [CommRing S] {A B B' C D : _root_.SerrePositivity.DifferentialGraded.Complex S}
variable (s : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ComplexSquareData A B C D) (m : B ⟶ B') (r : B' ⟶ D) (hr : m ≫ r = s.right)

/-- 下三角形の比較と上三角形の定値写像は対角上で一致する。 -/
lemma changeBottomMiddleHomotopy_compatible :
    ((SSet.stdSimplex.δ (1 : Fin 3)) ▷ (Δ[1] : SSet.{u + 1})) ≫
        (CartesianMonoidalCategory.fst (Δ[2] : SSet.{u + 1}) Δ[1] ≫
          (SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve S (Complex S))).symm s.upperTriangle) =
      ((SSet.stdSimplex.δ (1 : Fin 3)) ▷ (Δ[1] : SSet.{u + 1})) ≫
        (s.changeBottomMiddleLowerHomotopy m r hr).h := by
  calc
    _ = CartesianMonoidalCategory.fst (Δ[1] : SSet.{u + 1}) Δ[1] ≫
        SSet.stdSimplex.δ (1 : Fin 3) ≫
          (SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve S (Complex S))).symm s.upperTriangle := rfl
    _ = CartesianMonoidalCategory.fst (Δ[1] : SSet.{u + 1}) Δ[1] ≫
        SSet.stdSimplex.δ (1 : Fin 3) ≫
          (SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve S (Complex S))).symm s.lowerTriangle :=
      congrArg (fun q => CartesianMonoidalCategory.fst (Δ[1] : SSet.{u + 1}) Δ[1] ≫ q)
        s.triangles_compatible
    _ = _ := (s.changeBottomMiddleLowerHomotopy_diagonal m r hr).symm

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ComplexSquareData export _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories (changeBottomMiddleHomotopy_compatible)


/-- 右下の頂点を変更する実際の正方形ホモトピー。 -/
def changeBottomMiddleHomotopy : SSet.Homotopy s.square (s.changeBottomMiddle m r hr).square where
  h := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squarePrism_isPushout.desc
    (CartesianMonoidalCategory.fst (Δ[2] : SSet.{u + 1}) Δ[1] ≫
      (SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve S (Complex S))).symm s.upperTriangle)
    (s.changeBottomMiddleLowerHomotopy m r hr).h (s.changeBottomMiddleHomotopy_compatible m r hr)
  h₀ := by
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.square_isPushout.hom_ext
    · rw [← Category.assoc, ← SSet.ι₀_comp, Category.assoc, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squarePrism_isPushout.inl_desc,
        ← Category.assoc, SSet.ι₀_fst, Category.id_comp]
      exact s.square_upper.symm
    · rw [← Category.assoc, ← SSet.ι₀_comp, Category.assoc, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squarePrism_isPushout.inr_desc]
      exact (s.changeBottomMiddleLowerHomotopy m r hr).h₀.trans s.square_lower.symm
  h₁ := by
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.square_isPushout.hom_ext
    · rw [← Category.assoc, ← SSet.ι₁_comp, Category.assoc, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squarePrism_isPushout.inl_desc,
        ← Category.assoc, SSet.ι₁_fst, Category.id_comp]
      exact (s.changeBottomMiddle m r hr).square_upper.symm
    · rw [← Category.assoc, ← SSet.ι₁_comp, Category.assoc, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squarePrism_isPushout.inr_desc]
      exact (s.changeBottomMiddleLowerHomotopy m r hr).h₁.trans
        (s.changeBottomMiddle m r hr).square_lower.symm
  rel := by
    ext n q
    exact False.elim q.1.2

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ComplexSquareData export _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories (changeBottomMiddleHomotopy)


/-- 正方形比較の上三角形への制限は元の上三角形の定値ホモトピー。 -/
lemma changeBottomMiddleHomotopy_upper :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 0 ▷ (Δ[1] : SSet.{u + 1})) ≫ (s.changeBottomMiddleHomotopy m r hr).h =
      CartesianMonoidalCategory.fst (Δ[2] : SSet.{u + 1}) Δ[1] ≫
        (SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve S (Complex S))).symm s.upperTriangle :=
  _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squarePrism_isPushout.inl_desc _ _ _

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ComplexSquareData export _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories (changeBottomMiddleHomotopy_upper)


/-- 正方形比較は下三角形の中間対象の変更を保つ。 -/
lemma changeBottomMiddleHomotopy_lower :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle 1 ▷ (Δ[1] : SSet.{u + 1})) ≫ (s.changeBottomMiddleHomotopy m r hr).h =
      (s.changeBottomMiddleLowerHomotopy m r hr).h :=
  _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squarePrism_isPushout.inr_desc _ _ _

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ComplexSquareData export _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories (changeBottomMiddleHomotopy_lower)


end SerrePositivity.InfinityCategories.Project.DerivedCategories
