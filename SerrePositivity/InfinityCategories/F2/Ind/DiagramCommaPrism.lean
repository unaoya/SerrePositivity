module

public import SerrePositivity.InfinityCategories.F2.Ind.DiagramComma
public import SerrePositivity.InfinityCategories.F1.FunctorCategories.FunctorFiber

/-!
概要：元の図式 comma の全試験族を、指定図式への元の全円柱として読む。
方針：標準全余錐を試験族で制限し、内部 Hom の随伴で全写像を取り出す。
規約：元の C 側の全図式と終端の指定図式を保持。使われ方：終点 comma の円柱族。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
variable (κ : Cardinal.{u}) {K C : SSet.{u}} [Quasicategory C]
  (D : (SSet.uliftFunctor.{u + 1, u}).obj K ⟶ IndInfinity κ C)
  {T : SSet.{u + 1}} (q : T ⟶ diagramComma κ D)

/-- 元の全変換族をそのまま実現する、指定元図式への全円柱。 -/
def diagramCommaPrism : (SSet.uliftFunctor.{u + 1, u}).obj K ⊗
    join T (Δ[0] : SSet.{u + 1}) ⟶ IndInfinity κ C :=
  uncurry (joinMap q (𝟙 Δ[0]) ≫ (diagramCommaCocone κ D).val)

/-- 元の試験族側の全制限は、同じ C 側の全図式の Yoneda 像。 -/
lemma diagramCommaPrism_old :
    ((SSet.uliftFunctor.{u + 1, u}).obj K ◁ joinInl T (Δ[0] : SSet.{u + 1})) ≫
      diagramCommaPrism κ D q =
        uncurry (q ≫ diagramCommaProjection κ D ≫ (uliftFunctorSpaceIso K C).hom) ≫
          indYoneda κ C := by
  rw [diagramCommaPrism, ← uncurry_natural_left, ← Category.assoc, joinInl_joinMap,
    Category.assoc, (diagramCommaCocone κ D).property]
  simp only [diagramYoneda, ← Category.assoc, uncurry_natural_right]

/-- 余錐の終端側の全制限は、同じ元の指定図式そのもの。 -/
lemma diagramCommaPrism_tip :
    ((SSet.uliftFunctor.{u + 1, u}).obj K ◁ joinInr T (Δ[0] : SSet.{u + 1})) ≫
      diagramCommaPrism κ D q =
        fst ((SSet.uliftFunctor.{u + 1, u}).obj K) (Δ[0] : SSet.{u + 1}) ≫ D := by
  rw [diagramCommaPrism, ← uncurry_natural_left, ← Category.assoc, joinInr_joinMap,
    Category.id_comp]
  have ht : joinInr (diagramComma κ D) (Δ[0] : SSet.{u + 1}) ≫
      (diagramCommaCocone κ D).val = SSet.const (functorVertex D) := by
    change joinInr _ _ ≫ sliceOverUncurry _ = _
    rw [sliceOverUncurry_fixed, SSet.yonedaEquiv_symm_zero]
  rw [ht, uncurry_const_functorVertex]

end SerrePositivity.InfinityCategories.F2.Ind
