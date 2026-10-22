module

public import SerrePositivity.InfinityCategories.F2.CoherentCoconeUniversalTransportComponent
public import SerrePositivity.InfinityCategories.F2.CoherentColimitIntervalTransportAnchors
public import SerrePositivity.InfinityCategories.F2.CoherentCospanModelNativeLegCompatibility

/-!
概要：a6 の正方形の native 成分の像を、全 Hom の同じ普遍作用成分へ同定する。
方針：元の fiber 輸送頂点の表示変更だけを除き、同じ普遍成分を写す。
規約：元の指定成分を保持。使われ方：完成済み比較と模型三角形の共有成分の消去。
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
local notation "x" => JoinCocone.vertex (coherentDiagramTotalCocone F)
local notation "z" => coherentDiagramTotalVertex G
local notation "q" => pinchedHomLeftToIntervalMappingSpace x z
local notation "a" => coherentTransformationTotalMap F G (coherentVertexOfHomotopy H)
local notation "n" => Sigma.fst (coherentTotalMapNativeRepresentation F G a)
local notation "en" => FunctorIso.app (pointedIntervalTransport_mapIso q) n

/-- 元の native 成分は、同じ元の普遍輸送成分の頂点表示変更だけで得られる。 -/
lemma coherentColimitIntervalNativeTransportIso_heq_component :
    HEq (coherentColimitIntervalNativeTransportIso B H) en := by
  unfold coherentColimitIntervalNativeTransportIso
  dsimp only
  exact iso_eqToIso_trans_heq _ en

/-- 元の native 成分の fiber・値への像は、全 Hom の同じ普遍輸送成分と値まで一致。 -/
lemma coherentColimitIntervalNativeTransportIso_action_heq :
    HEq (VertexIso.map (coherentColimitIntervalNativeTransportIso B H)
      (coherentCoconeFiberValueAction F (coherentDiagramTotalCocone F) z))
      ((coherentCoconeUniversalTransportIso F (coherentDiagramTotalCocone F) z).app n) := by
  have ha : functorVertex (coherentTotalMapNativeFiberTransport F G a) =
      (pointedIntervalTransport q).map.app (Opposite.op ⦋0⦌) n :=
    (functorVertexEquiv _ _).apply_symm_apply _
  have he := vertexIso_map_heq_of_heq (coherentColimitIntervalNativeTransportIso B H) en
    ha rfl (coherentColimitIntervalNativeTransportIso_heq_component B H)
    (coherentCoconeFiberValueAction F (coherentDiagramTotalCocone F) z)
  exact he.trans (coherentCoconeUniversalTransportIso_app_heq F
    (coherentDiagramTotalCocone F) z n).symm

/-- 元の native 成分の作用の始点は、同じ全 Hom 作用の実際の始点と等しい。 -/
lemma coherentColimitIntervalNativeActionSource_eq :
    (coherentCoconeFiberValueAction F (coherentDiagramTotalCocone F) z).app (Opposite.op ⦋0⦌)
      (functorVertex (coherentTotalMapNativeFiberTransport F G a)) =
    (coherentCoconeTransportAction F (coherentDiagramTotalCocone F) z).app (Opposite.op ⦋0⦌) n := by
  exact congrArg (fun v =>
    (coherentCoconeFiberValueAction F (coherentDiagramTotalCocone F) z).app (Opposite.op ⦋0⦌) v)
    ((functorVertexEquiv _ _).apply_symm_apply _)

/-- 同じ始点の表示変更後には、元の native 成分の像と全 Hom 成分は等式で一致する。 -/
lemma coherentColimitIntervalNativeTransportIso_action_eq :
    vertexIsoOfEq (VertexIso.map (coherentColimitIntervalNativeTransportIso B H)
      (coherentCoconeFiberValueAction F (coherentDiagramTotalCocone F) z))
      (coherentColimitIntervalNativeActionSource_eq B H) rfl =
      (coherentCoconeUniversalTransportIso F (coherentDiagramTotalCocone F) z).app n := by
  exact eq_of_heq ((vertexIsoOfEq_heq _ _ _).trans
    (coherentColimitIntervalNativeTransportIso_action_heq B H))

end SerrePositivity.InfinityCategories.F2
