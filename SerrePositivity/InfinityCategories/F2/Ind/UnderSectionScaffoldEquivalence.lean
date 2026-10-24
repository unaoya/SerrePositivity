module

public import SerrePositivity.InfinityCategories.F2.Ind.UnderSectionScaffoldHorizontal
public import SerrePositivity.InfinityCategories.F2.Ind.ProductGraphFiber
public import SerrePositivity.InfinityCategories.F2.Ind.UnderSectionWeightedNerve
public import SerrePositivity.InfinityCategories.F1.Weighted.NerveCocartesianScaffold

/-!
概要：元の under scaffold の大域評価と同じ taut scaffold は、両方とも前合成同値。
方針：元の水平辺と元の評価の fiber 同値を、既存の cocartesian scaffold 定理へ渡す。
規約：共同全空間への射自体を比較し、replacement に充填性を仮定しない。
使われ方：元の共同 left fibration と strict weighted nerve の底上の復元 span。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
namespace SerrePositivity.InfinityCategories.F2.Ind
variable {I : Type u} [Category.{u} I] {B E : SSet.{u}} [Quasicategory B]
  (p : E ⟶ B ⊗ nerve I) [LeftFibration p]

local instance (i : I) : Quasicategory (vertexFiber (p ≫ snd B (nerve I)) (nerveVertex i)) :=
  vertexFiber_quasicategory_of_innerFibration _ _

/-- 元の添字上の fiber 比較は、元の評価とグラフ fiber 同型の合成。 -/
lemma underSectionScaffold_fiber (i : I) :
    SerrePositivity.InfinityCategories.leftScaffoldFiberMap (p ≫ snd B (nerve I)) (underSectionTotalDiagram p)
      (underSectionScaffold p) (underSectionScaffold_projection p) i =
        underSectionEvaluate p i ≫ (productGraphFiberIso p i).hom := by
  apply vertexFiber_hom_ext
  change simplicialReplacementConstantLift (underSectionTotalDiagram p) i ≫
    underSectionScaffold p = (underSectionEvaluate p i ≫ (productGraphFiberIso p i).hom) ≫ _
  rw [Category.assoc, productGraphFiberIso_ι, underSectionScaffold_value]

/-- 同じ元の大域評価は cocartesian scaffold の全条件を満たす。 -/
lemma underSectionScaffold_isCocartesianScaffold :
    SerrePositivity.InfinityCategories.CocartesianScaffold (p ≫ snd B (nerve I))
      (underSectionTotalDiagram p) (underSectionScaffold p) where
  projection := underSectionScaffold_projection p
  horizontal := underSectionScaffold_horizontal p
  fiber i := by
    rw [underSectionScaffold_fiber]
    exact (underSectionEvaluate_isQCatEquivalence p i).comp
      (qCatEquivalenceOfIso (productGraphFiberIso p i)).isQCatEquivalence

/-- 元の共同全空間への大域評価自体は前合成同値。 -/
lemma underSectionScaffold_isPrecompositionEquivalence :
    IsPrecompositionEquivalence (underSectionScaffold p) :=
  (underSectionScaffold_isCocartesianScaffold p).isPrecompositionEquivalence

/-- 同じ底上の taut scaffold 自体も前合成同値。 -/
lemma underSectionTautScaffold_isPrecompositionEquivalence :
    IsPrecompositionEquivalence (tautScaffold (underSectionTotalDiagram p)) :=
  tautScaffold_isPrecompositionEquivalence_of_quasicategory _

end SerrePositivity.InfinityCategories.F2.Ind
