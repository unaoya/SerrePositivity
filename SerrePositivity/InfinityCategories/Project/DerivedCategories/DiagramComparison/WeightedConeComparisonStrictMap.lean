module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.CoherentComparisonStrictNaturality
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.WeightedConeHomNaturality

/-!
概要：元のweighted coneの厳密自然性を、同じcoherent比較の全HA写像にまとめる。
方針：検証済みの全豊穣Homの自然性と同じcoherent比較の係数自然性を合成。
規約：IS-W2 D01の既存構成の自然性・貼り合わせ則。元の閉零成分と高次成分を保つ。
使われ方：HA 1.2.4、StrictCoherentFamilyによる全パラメータ錐族の構成。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
open CategoryTheory
open SerrePositivity.DifferentialGraded
open SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
variable {R : Type u} [CommRing R] {D : Type v} [DGCategory R D]
variable {I : Type u} [SmallCategory I] {F G : I ⥤ ClosedCategory R D}

/-- 同じweighted cone単体の全高次HA成分に可換する指定写像。 -/
def weightedConeComparisonStrictMap {n : ℕ} {σ : ComposableArrows I n}
    (η : F ⟶ G) {x y : ClosedCategory R D} (f : x ⟶ y)
    (τ : simplexPrefixWeight n ⟶ σ ⋙ simplicialHomDiagram F x ⋙ SSet.opFunctor)
    (τ' : simplexPrefixWeight n ⟶ σ ⋙ simplicialHomDiagram G y ⋙ SSet.opFunctor)
    (h : τ ≫ Functor.whiskerLeft σ
        (Functor.whiskerRight (weightedConeHomTargetMap η x) SSet.opFunctor) =
      τ' ≫ Functor.whiskerLeft σ
        (Functor.whiskerRight (weightedConeHomSourceMap f G) SSet.opFunctor)) :
    StrictSimplexMap R D (coherentSimplexData (weightedConeSimplex F x τ))
      (coherentSimplexData (weightedConeSimplex G y τ')) :=
  coherentComparisonStrictMap (weightedConeSimplex F x τ) (weightedConeSimplex G y τ')
    (fun i => weightedConeVertexMap η f σ i.as.down)
    (fun i j => weightedConeHom_naturality η f τ τ' h i.as.down j.as.down)

end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
