module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.ReflectedBKFreeConeAdjunction
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.FreeNegativeStandardHomEvaluation
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplicialCategory

/-!
概要：元の反転BK錐入力の実標準Homの最上位成分を、同じ実代表の自由生成元で評価する。
方針：同じDK同型の両逆と指定自由鎖逆随伴の全次数評価を合成する。
規約：元の錐入力・標準DK同型・自由生成元を保持する既存構成の評価則。
使われ方：HA 1.2.4、IS-W2 B02のAW各切断の右辺の厳密な照合。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization
open CategoryTheory HomologicalComplex CochainComplex HomComplex AlgebraicTopology
open SerrePositivity.DifferentialGraded SerrePositivity.HomologicalAlgebra
open SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
open SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
open scoped Simplicial
variable {A : Type u} [CommRing A]
local notation "V" => Functor.flip (Functor.obj SimplicialObject.opFunctor bousfieldKanSetWeight)

/-- 元の指定反転錐の標準Hom像の最上位成分は、実A12代表の同じ自由生成元の像。 -/
theorem reflectedBKFreeCone_generator_top (X : CosimplicialObject (Complex A))
    (j : SimplexCategoryᵒᵖᵒᵖ) (n : ℕ)
    (s : ((V ⋙ SSet.uliftFunctor.{u,0}).obj j).obj (Opposite.op ⦋n⦌)) :
    let T := (productTotalFunctor A).obj X
    let Q := (doubleOppositeDiagram X).obj j
    let g := (reversedWeightPointwiseBousfieldKanCone X).app j ≫
      (Functor.isoWhiskerRight (standardDoldKanModuleIso (R := A) (D := Complex A) T Q)
        (forget (ModuleCat A))).inv
    (((((normalizedLinearWeightDiagramIso A V).inv ≫
      extendMap (normalizedMooreReverse.app (linearizedSimplicialWeight A bousfieldKanSetWeight))
        ComplexShape.embeddingDownNat) ≫ normalizedBousfieldKanConeRepresentative X).f
          (-(n : ℤ))).app j) (freeNegativeGenerator ((V ⋙ SSet.uliftFunctor.{u,0}).obj j) n s) =
      standardTopEval (R := A) T Q n (g.app _ s) := by
  dsimp only
  let S := (V ⋙ SSet.uliftFunctor.{u,0}).obj j
  let T := (productTotalFunctor A).obj X
  let Q := (doubleOppositeDiagram X).obj j
  let e := Functor.isoWhiskerRight
    (standardDoldKanModuleIso (R := A) (D := Complex A) T Q) (forget (ModuleCat A))
  let g := (reversedWeightPointwiseBousfieldKanCone X).app j ≫ e.inv
  have hη := ConcreteCategory.congr_hom
    (reversedWeightPointwiseBousfieldKanCone_point_inverse_f X j (-(n : ℤ)))
    (freeNegativeGenerator S n s)
  have ht := freeNegativeStandardHom_generator_eval S T Q g n s
  have he : g ≫ standardDoldKanSpaceMap T Q =
      (reversedWeightPointwiseBousfieldKanCone X).app j := by
    change ((reversedWeightPointwiseBousfieldKanCone X).app j ≫ e.inv) ≫ e.hom = _
    rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have hta := congrArg (fun t =>
    (((freeNegativeChainsAdjunction A).homEquiv S (homObject A (Complex A) T Q)).symm t).f
      (-(n : ℤ)) (freeNegativeGenerator S n s)) he
  exact hη.symm.trans (hta.symm.trans ht)

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization
