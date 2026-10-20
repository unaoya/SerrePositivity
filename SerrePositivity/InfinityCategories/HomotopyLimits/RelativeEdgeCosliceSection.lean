module

public import SerrePositivity.InfinityCategories.HomotopyLimits.CosliceEdgeFamilies

/-!
概要：辺の終点側の全余錐族を、底の指定した合成切断と同時に辺全体へ延長する。
方針：相対 coslice の終点制限の自明 Kan 性を使う。
規約：同じ底の cosliceEdgeSection を厳密に保持。使われ方：初期 Hom 間の前置写像。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
noncomputable section
variable {E B : SSet.{u}} [Quasicategory B] (e : (Δ[1] : SSet.{u}) ⟶ E) (q : E ⟶ B)

/-- 終点の恒等族と、底の同じ合成切断による族は、相対持ち上げの入力として整合する。 -/
lemma relativeEdgeCosliceSection_compatible :
    (𝟙 (sliceUnder (stdSimplex.δ (0 : Fin 2) ≫ e))) ≫
        sliceUnderPostcomp (stdSimplex.δ (0 : Fin 2) ≫ e) q =
      (sliceUnderPostcomp (stdSimplex.δ (0 : Fin 2) ≫ e) q ≫ cosliceEdgeSection (e ≫ q)) ≫
        sliceUnderRestrict (e ≫ q) (stdSimplex.δ (0 : Fin 2)) := by
  simp only [Category.assoc, cosliceEdgeSection_target, Category.id_comp]
  exact (Category.comp_id _).symm

variable [InnerFibration q]

/-- 終点の全余錐空間を一度に延長し、底には同じ指定した切断を使う。 -/
def relativeEdgeCosliceSection : sliceUnder (stdSimplex.δ (0 : Fin 2) ≫ e) ⟶ sliceUnder e :=
  (exists_relativeEdgeCosliceLift e q (𝟙 _)
    (sliceUnderPostcomp (stdSimplex.δ (0 : Fin 2) ≫ e) q ≫ cosliceEdgeSection (e ≫ q))
    (relativeEdgeCosliceSection_compatible e q)).choose

/-- 相対切断は、入力した終点側の全族を厳密に回収する。 -/
lemma relativeEdgeCosliceSection_target :
    relativeEdgeCosliceSection e q ≫ sliceUnderRestrict e (stdSimplex.δ (0 : Fin 2)) = 𝟙 _ :=
  (exists_relativeEdgeCosliceLift e q (𝟙 _)
    (sliceUnderPostcomp (stdSimplex.δ (0 : Fin 2) ≫ e) q ≫ cosliceEdgeSection (e ≫ q))
    (relativeEdgeCosliceSection_compatible e q)).choose_spec.1

/-- 相対切断の底は、同じ元の底の合成切断そのもの。 -/
lemma relativeEdgeCosliceSection_base :
    relativeEdgeCosliceSection e q ≫ sliceUnderPostcomp e q =
      sliceUnderPostcomp (stdSimplex.δ (0 : Fin 2) ≫ e) q ≫ cosliceEdgeSection (e ≫ q) :=
  (exists_relativeEdgeCosliceLift e q (𝟙 _)
    (sliceUnderPostcomp (stdSimplex.δ (0 : Fin 2) ≫ e) q ≫ cosliceEdgeSection (e ≫ q))
    (relativeEdgeCosliceSection_compatible e q)).choose_spec.2

/-- 相対切断は、可変な終点の全単体を厳密に保つ。 -/
lemma relativeEdgeCosliceSection_projection :
    relativeEdgeCosliceSection e q ≫ sliceUnderProjection e =
      sliceUnderProjection (stdSimplex.δ (0 : Fin 2) ≫ e) := by
  rw [← sliceUnderRestrict_projection e (stdSimplex.δ (0 : Fin 2)), ← Category.assoc,
    relativeEdgeCosliceSection_target, Category.id_comp]

end
end SerrePositivity.InfinityCategories.HomotopyLimits
