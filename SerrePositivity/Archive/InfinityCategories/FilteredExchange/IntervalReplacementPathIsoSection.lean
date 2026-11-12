module

public import SerrePositivity.InfinityCategories.Project.FilteredExchange.IntervalReplacementPathSection
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.HomotopyConstantIso

/-!
概要：元の置換 path の指定同型は切断上で等式からの標準同型に簡約する。
方針：元の全円柱の定値性と前合成の辺の類の計算。
規約：元の指定同型を保持。使われ方：左脚の像比較と元の path の整合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {X Y : SSet.{u}} [KanComplex Y]

/-- 概要：任意の前合成の後も切断上の元の指定同型は等式から来る。
方針：元の定値円柱を辺の類へ移す。
規約：元の同型の値を変更しない。使われ方：交換則の切断側の簡約。 -/
lemma intervalReplacementPathIso_section_precomp_isFunctorEqIso
    {A : SSet.{u}} (f : X ⟶ Y) (a : A ⟶ X) :
    IsFunctorEqIso ((intervalReplacementPathIso f).precomp (a ≫ intervalReplacementSection f)) := by
  let H := intervalReplacementCanonicalPathHomotopy f
  let T := functorHomotopyPrecomp H (a ≫ intervalReplacementSection f)
  apply isFunctorEqIso_of_homotopy_constant T _
  · rw [functorIso_precomp_hom, intervalReplacementPathIso_hom]
    exact (functorHomotopyPrecomp_hom H (a ≫ intervalReplacementSection f)).symm
  · have hs : (a ≫ intervalReplacementSection f) ≫
        (pullback.snd ((intervalEndpointNatTrans 0).app Y) f ≫ f) = a ≫ f := by
      calc
        _ = a ≫ ((intervalReplacementSection f ≫
          pullback.snd ((intervalEndpointNatTrans 0).app Y) f) ≫ f) := by
            simp only [Category.assoc]
        _ = _ := by rw [intervalReplacementSection_projection, Category.id_comp]
    change ((a ≫ intervalReplacementSection f) ▷ (Δ[1] : SSet.{u})) ≫
      (intervalReplacementCanonicalPathHomotopy f).h = fst A (Δ[1] : SSet.{u}) ≫
        ((a ≫ intervalReplacementSection f) ≫
          (pullback.snd ((intervalEndpointNatTrans 0).app Y) f ≫ f))
    rw [hs]
    exact intervalReplacementCanonicalPathHomotopy_section_precomp f a

end SerrePositivity.InfinityCategories.F2
