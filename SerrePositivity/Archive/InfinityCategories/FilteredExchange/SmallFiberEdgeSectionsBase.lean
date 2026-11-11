module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.SmallFiberEdgeSections
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.RelativeConstFiberEvaluation

/-!
概要：元の fiber 作用を表す切断族を、同じ辺の任意の明示した図式表示へ移す。
方針：底の等式による同型だけを合成し、全円柱・両端評価・同値性を保持する。
規約：図式辺の等式を入力に保持。使われ方：元の native cospan の二辺との厳密な照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {B : SSet.{u}}
  (F G : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
  (x : (leftUnstraighteningTransformationSpace F G) _⦋0⦌) (b : B _⦋0⦌)
  (e : (Δ[1] : SSet.{u + 1}) ⟶ SpaceInfinity.{u})
  (he : e = coherentTransformationPointEdge F G x b)
local notation "a" => coherentNativeTriangleFiberParameters F b

/-- 同じ実際の fiber 作用の切断族を、指定した同じ辺の表示へ移す。 -/
def coherentSmallFiberEdgeSectionsOfEq : a ⟶ relativeFunctorSpace pointedSpaceProjection e :=
  coherentSmallFiberEdgeSections F G x b ≫
    eqToHom (congrArg (relativeFunctorSpace pointedSpaceProjection) he.symm)

/-- 底の表示を移しても、元の全 prism を厳密に回収する。 -/
lemma coherentSmallFiberEdgeSectionsOfEq_uncurry :
    relativeFunctorUncurry (coherentSmallFiberEdgeSectionsOfEq F G x b e he) =
      coherentSmallFiberPointedPrism F G x b := by
  subst e
  simp only [coherentSmallFiberEdgeSectionsOfEq, eqToHom_refl, Category.comp_id]
  exact relativeFunctorUncurry_curry _ _

/-- 指定した辺の表示でも、元の fiber から切断族への写像は同値である。 -/
lemma coherentSmallFiberEdgeSectionsOfEq_isQCatEquivalence :
    IsQCatEquivalence (coherentSmallFiberEdgeSectionsOfEq F G x b e he) :=
  (coherentSmallFiberEdgeSections_isQCatEquivalence F G x b).comp
    (qCatEquivalenceOfIso
      (eqToIso (congrArg (relativeFunctorSpace pointedSpaceProjection) he.symm))).isQCatEquivalence

/-- 始点の元の値を明示した評価でも、同じ恒等写像を回収する。 -/
lemma coherentSmallFiberEdgeSectionsOfEq_source
    (hv : e.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm 0) = F.app _ (ULift.up b)) :
    coherentSmallFiberEdgeSectionsOfEq F G x b e he ≫ pointedSectionSourceFiber F b e hv =
      𝟙 a := by
  subst e
  simpa only [coherentSmallFiberEdgeSectionsOfEq, eqToHom_refl, Category.comp_id] using
    coherentSmallFiberEdgeSections_source F G x b

/-- 終点の元の値を明示した評価でも、同じ実際の fiber 作用を回収する。 -/
lemma coherentSmallFiberEdgeSectionsOfEq_target
    (hv : e.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm 1) = G.app _ (ULift.up b)) :
    coherentSmallFiberEdgeSectionsOfEq F G x b e he ≫ pointedSectionTargetFiber G b e hv =
      (SSet.uliftFunctor.{u + 1, u}).map
        (vertexFiberMap (smallLeftUnstraighteningProjection F)
          (smallLeftUnstraighteningProjection G) (coherentTransformationTotalMap F G x)
          (coherentTransformationTotalMap_projection F G x) b) := by
  subst e
  simpa only [coherentSmallFiberEdgeSectionsOfEq, eqToHom_refl, Category.comp_id] using
    coherentSmallFiberEdgeSections_target F G x b

end SerrePositivity.InfinityCategories.F2
