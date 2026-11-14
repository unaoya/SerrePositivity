module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.NormalizedBKConeZeroRow
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.BKStandardZeroGenerator
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.StandardLeg
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.LinearWeightZeroGenerator
public import SerrePositivity.HomologicalAlgebra.NormalizedMooreReverseExtendZero
public import SerrePositivity.HomologicalAlgebra.FreeWeightEndInverseEvaluation

/-!
概要：元の反転BK錐代表の恒等射頂点での零次評価は、同じ第0頂点の標準脚。
方針：指定係数逆射、Moore反転、元の零行、自由単位重みの逆評価を同じ合成で結ぶ。
規約：IS-W2 C01の既存構成の評価・単位則。元の錐代表と生成元を保持する。
使われ方：HA 1.2.4、指定native錐の標準脚の最終照合。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization
open CategoryTheory CategoryTheory.Limits CochainComplex HomComplex HomologicalComplex AlgebraicTopology
open SerrePositivity.DifferentialGraded SerrePositivity.HomologicalAlgebra
open SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open scoped Simplicial
variable {A : Type u} [CommRing A]

/-- 同じ自由生成元で反転BK錐代表を零次評価すると、元の第0頂点の標準脚になる。 -/
theorem reflectedBKCone_zero_generator (X : CosimplicialObject (Complex A))
    (n : SimplexCategory) :
    let j := Opposite.op (Opposite.op n)
    let W := (SimplicialObject.opFunctor.obj bousfieldKanSetWeight).flip
    let S := (W ⋙ SSet.uliftFunctor.{u,0}).obj j
    (((((normalizedLinearWeightDiagramIso A W).inv ≫
      extendMap (normalizedMooreReverse.app (linearizedSimplicialWeight A bousfieldKanSetWeight))
        ComplexShape.embeddingDownNat) ≫ normalizedBousfieldKanConeRepresentative X).f 0).app j)
      (freeNegativeGenerator S 0 (ULift.up (nerveVertex (Over.mk (𝟙 n))))) =
    Cochain.ofHom (standardLeg A X n) := by
  let j := Opposite.op (Opposite.op n)
  let W := (SimplicialObject.opFunctor.obj bousfieldKanSetWeight).flip
  let V := linearizedSimplicialWeight A bousfieldKanSetWeight
  let N := normalizedBousfieldKanWeight (A := A)
  let Nr := (normalizedMooreComplex _).obj (SimplicialObject.opFunctor.obj V)
  let er := negativeChainRowIso Nr 0
  let e := negativeChainRowIso N 0
  let a := (normalizedLinearWeightDiagramIso A W).inv.f 0
  let r := extendMap (normalizedMooreReverse.app V) ComplexShape.embeddingDownNat
  let c := (barDoubleOppositeOverChainIso SimplexCategory (ModuleCat.of A A)).inv.f 0 ≫
    ((alternatingFaceMapComplex _).map
      (SimplicialRealization.barStandardWeightComparison (ModuleCat.of A A))).f 0
  let H := doubleOppositeDiagram ((homDiagramFunctor ((productTotalFunctor A).obj X)).obj X)
  let b := ((freeUnitWeightEndNatIso A (Opposite.op ⦋0⦌)).inv.app H).f 0
    (Cochain.ofHom (standardZeroLeg A X))
  have hrep := (Iso.inv_comp_eq (negativeChainRowIso (normalizedBousfieldKanWeight (A := A)) 0)).mp
    (normalizedBousfieldKanConeRepresentative_zero_row X)
  have hp : r.f 0 ≫ e.hom ≫ (inclusionOfMooreComplexMap V).f 0 =
      er.hom ≫ (inclusionOfMooreComplexMap (SimplicialObject.opFunctor.obj V)).f 0 :=
    normalizedMooreReverse_extend_zero_inclusion V
  have hpa := congrArg (fun f => a ≫ f ≫ c ≫ b) hp
  simp only [Category.assoc] at hpa
  have hg := normalizedLinearWeightDiagramIso_inv_zero_generator A W j
    (nerveVertex (Over.mk (𝟙 n)))
  dsimp only
  simp only [HomologicalComplex.comp_f]
  refine (congrArg (fun f => ((a ≫ r.f 0 ≫ f).app j)
    (freeNegativeGenerator ((W ⋙ SSet.uliftFunctor.{u,0}).obj j) 0
      (ULift.up (nerveVertex (Over.mk (𝟙 n)))))) hrep).trans ?_
  dsimp only [normalizedBKStandardWeightMap, HomologicalComplex.comp_f]
  simp only [Category.assoc]
  change ((a ≫ r.f 0 ≫ e.hom ≫ (inclusionOfMooreComplexMap V).f 0 ≫ c ≫ b).app j)
    (freeNegativeGenerator ((W ⋙ SSet.uliftFunctor.{u,0}).obj j) 0
      (ULift.up (nerveVertex (Over.mk (𝟙 n))))) = _
  refine (congrArg (fun f => f.app j
    (freeNegativeGenerator ((W ⋙ SSet.uliftFunctor.{u,0}).obj j) 0
      (ULift.up (nerveVertex (Over.mk (𝟙 n)))))) hpa).trans ?_
  change (b.app j) ((c.app j)
    (((inclusionOfMooreComplexMap (SimplicialObject.opFunctor.obj V)).f 0).app j
      (er.hom.app j ((a.app j)
        (freeNegativeGenerator ((W ⋙ SSet.uliftFunctor.{u,0}).obj j) 0
          (ULift.up (nerveVertex (Over.mk (𝟙 n))))))))) = _
  refine (congrArg (fun x => (b.app j) ((c.app j) x)) hg).trans ?_
  refine (congrArg (fun x => (b.app j) x) (barOverStandard_zero_generator A n)).trans ?_
  erw [freeUnitWeightEndNatIso_inv_generator]
  change (Cochain.ofHom (standardZeroLeg A X)).comp
    (Cochain.ofHom (X.map (SimplexCategory.const ⦋0⦌ n 0))) (zero_add 0) =
      Cochain.ofHom (standardZeroLeg A X ≫ X.map (SimplexCategory.const ⦋0⦌ n 0))
  exact (Cochain.ofHom_comp _ _).symm

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization
