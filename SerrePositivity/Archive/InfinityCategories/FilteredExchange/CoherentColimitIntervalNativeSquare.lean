module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentColimitIntervalNativeImage
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentColimitIntervalTransportAnchors

/-!
概要：a6 で実際に選んだ区間 native 比較の像を、元の二成分の指定正方形として保持する。
方針：構成時の同じ像を分解し、同じ completed 成分の逆を消去する。
規約：選択済み比較を保持。使われ方：完成済み三角形比較の値の一意的な照合。
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
local notation "y" => coherentDiagramTotalVertex G
local notation "P" => parametrizedFiberTransport pointedSpaceProjection x y

/-- 元の像は、構成時の同じ二成分と元の fiber 輸送比較の合成そのもの。 -/
lemma coherentColimitIntervalNativeImageIso_eq_anchors :
    coherentColimitIntervalNativeImageIso B H =
      (coherentColimitIntervalCompletedTransportIso B H).symm ≪≫
        coherentColimitFiberTransportIso B H ≪≫
          coherentColimitIntervalNativeTransportIso B H := by
  rfl

/-- a6 の元の選択済み比較は、同じ completed・native 成分と元の輸送比較の正方形を満たす。 -/
lemma coherentColimitIntervalNativeIso_square :
    coherentColimitIntervalCompletedTransportIso B H ≪≫
      VertexIso.map (coherentColimitIntervalNativeIso B H) P =
      coherentColimitFiberTransportIso B H ≪≫ coherentColimitIntervalNativeTransportIso B H := by
  rw [coherentColimitIntervalNativeIso_image, coherentColimitIntervalNativeImageIso_eq_anchors]
  simp only [← Iso.trans_assoc, Iso.self_symm_id, Iso.refl_trans]

/-- 同じ元の指定正方形を満たす比較は、a6 の元の選択済み比較に値まで一致する。 -/
lemma coherentColimitIntervalNativeIso_unique
    (n : VertexIso (coherentColimitIntervalVertex B H)
      ((pinchedHomLeftToIntervalMappingSpace x y).app (Opposite.op ⦋0⦌)
        (coherentTotalMapNativeRepresentation F G
          (coherentTransformationTotalMap F G (coherentVertexOfHomotopy H))).1))
    (hn : coherentColimitIntervalCompletedTransportIso B H ≪≫ VertexIso.map n P =
      coherentColimitFiberTransportIso B H ≪≫ coherentColimitIntervalNativeTransportIso B H) :
    n = coherentColimitIntervalNativeIso B H := by
  have hf := (parametrizedPointedSpaceTransport_isQCatEquivalence x y).isFullyFaithful
  apply vertexIso_map_injective hf
  change VertexIso.map n P = VertexIso.map (coherentColimitIntervalNativeIso B H) P
  have h := hn.trans (coherentColimitIntervalNativeIso_square B H).symm
  have hh := congrArg
    (fun k => (coherentColimitIntervalCompletedTransportIso B H).symm ≪≫ k) h
  simpa only [← Iso.trans_assoc, Iso.symm_self_id, Iso.refl_trans] using hh

end SerrePositivity.InfinityCategories.F2
