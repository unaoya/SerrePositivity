module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentColimitUpperNativeFactorPresentation

/-!
概要：模型側の同じ native 成分と上側 native 因子の実両端を照合する。
方針：元の単位自然性・頂点表示の往復だけで端点を揃える。
規約：元の native 因子を保持。使われ方：a6 模型正方形で上側因子を厳密に消去。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable (B : SSet.{u})
  {F G : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}} (H : SSet.Homotopy F G)
local notation "a" => coherentTransformationTotalMap F G (coherentVertexOfHomotopy H)
local notation "z" => coherentDiagramTotalVertex G
local notation "n" => Sigma.fst (coherentTotalMapNativeRepresentation F G a)

/-- 模型成分の実終点と上側 native 因子の元の単位終点は、同じ単位自然性で等しい。 -/
lemma coherentColimitNativeModelTarget_eq_unit :
    (smallLeftUnstraighteningIso F).inv ≫ (SSet.uliftFunctor.{u + 1, u}).map
      (coherentDiagramTotalUnit F ≫ coherentTotalVertexMap F G a) =
    (smallLeftUnstraighteningIso F).inv ≫ (SSet.uliftFunctor.{u + 1, u}).map
      (a ≫ coherentDiagramTotalUnit G) := by
  exact (coherentTotalMapNativeActionComponents_target F G a).trans
    (coherentColimitNativeAction_unit_lift B H)

/-- 模型成分の実始点は、元の native 作用射の同じ頂点表示と等しい。 -/
lemma coherentColimitNativeModelSource_eq_action :
    (coherentCoconeTransportAction F (coherentDiagramTotalCocone F) z).app
      (Opposite.op ⦋0⦌) n = functorVertex (coherentTotalMapNativeAction F G a) := by
  exact ((functorVertexEquiv _ _).apply_symm_apply _).symm

/-- 同じ両端を照合した上側 native 因子の逆は、元の模型成分と値まで一致する。 -/
lemma coherentColimitUpperNativeFactorIso_symm_heq_components :
    HEq (coherentColimitUpperNativeFactorIso B H).symm
      (coherentTotalMapNativeActionComponentsIso F G a) := by
  have h := vertexIso_symm_heq_of_heq (coherentColimitUpperNativeFactorIso B H)
    (coherentTotalMapNativeActionComponentsIso F G a).symm
    (congrArg functorVertex (coherentColimitNativeModelTarget_eq_unit B H).symm)
    (coherentColimitNativeModelSource_eq_action B H).symm
    (coherentColimitUpperNativeFactorIso_heq_components B H)
  simpa only [Iso.symm_symm_eq] using h

end SerrePositivity.InfinityCategories.F2
