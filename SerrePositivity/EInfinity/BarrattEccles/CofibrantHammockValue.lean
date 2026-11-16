module

public import SerrePositivity.EInfinity.BarrattEccles.CofibrantZigzagValue
public import SerrePositivity.EInfinity.BarrattEccles.CofibrantHammockInclusionLaws
public import SerrePositivity.EInfinity.BarrattEccles.MappingSpaceHammockComponentsValue

/-!
# HomLift を通る元の cofibrant hammock 包含と全語の評価

概要：既存の包含写像そのものの評価を元の局所化 Hom 作用へ同定する。
方針：全語の元の正規化式と元の zigzag の値を使用する。
規約：既存の包含・HomLift 同型・全単体を保持する。
使われ方：高次 DK/Map^h 比較が誘導する π₀ の既存同値との一致。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory _root_.HomotopicalAlgebra Hammock
variable (A : Type u) [CommRing A] (X Y : CofibrantAlgebra A)

lemma cofibrantAlgebraHammockInclusionMap_value :
    let := modelCategory A
    cofibrantAlgebraHammockInclusionMap A
        (cofibrantAlgebraDKObject A X) (cofibrantAlgebraDKObject A Y) ≫
      algebraReducedHammockValue A ((cofibrantAlgebraInclusion A).obj X)
        ((cofibrantAlgebraInclusion A).obj Y) =
    Zigzag.Value.reducedValue (cofibrantAlgebraRelativeCategory A).weakEquivalences.Q
        (cofibrantAlgebraRelativeCategory A).weakEquivalences.Q_inverts
        (cofibrantAlgebraDKObject A X) (cofibrantAlgebraDKObject A Y) ≫
      (Functor.const SimplexCategoryᵒᵖ).map (↾cofibrantAlgebraDKHoHomMap A X Y) := by
  let := modelCategory A
  let W := (cofibrantAlgebraRelativeCategory A).weakEquivalences
  let x := cofibrantAlgebraDKObject A X
  let y := cofibrantAlgebraDKObject A Y
  apply (cancel_epi (reducedColimitIso W x y).hom).1
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph_hom_ext
  intro w
  simp only [← Category.assoc]
  rw [reducedColimitIso_hom_fac, cofibrantAlgebraHammockInclusionMap_normalization]
  dsimp only [algebraReducedHammockValue]
  rw [Category.assoc]
  change cofibrantAlgebraHammockGraphInclusionMap A x y w ≫
      (graphNormalization (weakEquivalences (operad A).Algebra)
        ((cofibrantAlgebraDKInclusion A).obj x) ((cofibrantAlgebraDKInclusion A).obj y) w ≫
        UniverseValue.reducedValue (weakEquivalences (operad A).Algebra).Q
          (weakEquivalences (operad A).Algebra).Q_inverts
          ((cofibrantAlgebraDKInclusion A).obj x) ((cofibrantAlgebraDKInclusion A).obj y)) =
    (graphNormalization W x y w ≫ Zigzag.Value.reducedValue W.Q W.Q_inverts x y) ≫
      (Functor.const SimplexCategoryᵒᵖ).map (↾cofibrantAlgebraDKHoHomMap A X Y)
  rw [UniverseValue.graphNormalization_reducedValue, Zigzag.Value.graphNormalization_reducedValue]
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro σ
  exact cofibrantAlgebraZigzagValue_inclusion A w X Y (σ.obj 0)

lemma cofibrantAlgebraHammockInclusionMap_components_value
    (z : SSet.π₀ (reducedSimplicialSet
      (cofibrantAlgebraRelativeCategory A).weakEquivalences
      (cofibrantAlgebraDKObject A X) (cofibrantAlgebraDKObject A Y))) :
    let := modelCategory A
    algebraReducedHammockPiZeroValue A ((cofibrantAlgebraInclusion A).obj X)
        ((cofibrantAlgebraInclusion A).obj Y)
        (SSet.mapπ₀ (cofibrantAlgebraHammockInclusionMap A
          (cofibrantAlgebraDKObject A X) (cofibrantAlgebraDKObject A Y)) z) =
      cofibrantAlgebraDKHoHomMap A X Y (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.toComponents
        (Zigzag.Value.reducedValue (cofibrantAlgebraRelativeCategory A).weakEquivalences.Q
          (cofibrantAlgebraRelativeCategory A).weakEquivalences.Q_inverts
          (cofibrantAlgebraDKObject A X) (cofibrantAlgebraDKObject A Y)) z) := by
  let := modelCategory A
  obtain ⟨p, rfl⟩ := SSet.π₀.mk_surjective z
  exact congrArg (fun m => m.app (Opposite.op (SimplexCategory.mk 0)) p)
    (cofibrantAlgebraHammockInclusionMap_value A X Y)

end SerrePositivity.EInfinity.BarrattEccles
