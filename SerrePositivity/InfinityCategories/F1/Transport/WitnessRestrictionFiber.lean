module

public import SerrePositivity.InfinityCategories.F1.Transport.WitnessRestrictionLifting

/-!
概要：全頂点を含む底への表現空間の制限 fiber は周囲の四角形の制限 fiber と同型。
方針：制限先の頂点条件から元の頂点条件を反映し、全部分複体へ戻す。
規約：境界上で指定された表現を厳密に固定する。
使われ方：区間の四角形 fiber の可縮性を実際の表現空間へ移す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

local instance {E B D : SSet.{u}} (p : E ⟶ B) [LeftFibration p] (g : D ⟶ B) :
    LeftFibration (pullback.snd p g) :=
  ⟨leftFibrations.pullback_snd p g (LeftFibration.mem (p := p))⟩

/-- 概要：全頂点を被覆する底変換の表現制限 fiber は周囲の四角形の fiber と厳密に同型。
方針：fiber の包含の全頂点で表現条件を反映して全部分複体へ持ち上げる。
規約：単射性と充填性は底変換に要求しない。
使われ方：実際の区間表現空間の境界 fiber の可縮性。 -/
def transportWitnessRestrictionFiberIso {E B D : SSet.{u + 1}}
    (p : E ⟶ B) [LeftFibration p] (g : D ⟶ B)
    (hg : Function.Surjective (g.app (Opposite.op ⦋0⦌)))
    (v : (transportWitnessSpace (pullback.snd p g)) _⦋0⦌) :
    vertexFiber (transportWitnessRestriction p g) v ≅
      vertexFiber (transportSquareRestriction p g) v.val := by
  let w := transportWitnessRestriction p g
  let q := transportSquareRestriction p g
  let S := vertexFiber w v
  let T := vertexFiber q v.val
  let ιS := vertexFiberι w v
  let ιT := vertexFiberι q v.val
  have hFcond : (ιS ≫ transportWitnessSpaceι p) ≫ q = SSet.const v.val := by
    rw [Category.assoc, ← transportWitnessRestriction_ι, ← Category.assoc]
    change (ιS ≫ w) ≫ transportWitnessSpaceι (pullback.snd p g) = _
    rw [vertexFiberι_comp, SSet.const_comp]
    rfl
  let F : S ⟶ T := vertexFiberLift q v.val (ιS ≫ transportWitnessSpaceι p) hFcond
  have hF : F ≫ ιT = ιS ≫ transportWitnessSpaceι p := vertexFiberLift_ι _ _ _ _
  have hv : ∀ x : T _⦋0⦌, IsTransportWitnessVertex p (ιT.app _ x) := by
    intro x
    apply isTransportWitnessVertex_of_restriction p g hg
    have hx := congrArg (fun f ↦ f.app (Opposite.op ⦋0⦌) x) (vertexFiberι_comp q v.val)
    change q.app _ (ιT.app _ x) = (SSet.const v.val : T ⟶ _).app _ x at hx
    simp only [SSet.const_app, SimplexCategory.const_eq_id, op_id, Functor.map_id_apply] at hx
    rw [hx]
    exact fullSubcomplexOnVertices_vertex v
  let G₀ := fullSubcomplexLift (IsTransportWitnessVertex p) ιT hv
  have hG₀ : G₀ ≫ transportWitnessSpaceι p = ιT := fullSubcomplexLift_ι _ _ _
  have hGcond : G₀ ≫ w = SSet.const v := by
    apply (cancel_mono (transportWitnessSpaceι (pullback.snd p g))).1
    rw [Category.assoc, transportWitnessRestriction_ι, ← Category.assoc, hG₀,
      SSet.const_comp]
    exact vertexFiberι_comp q v.val
  let G : T ⟶ S := vertexFiberLift w v G₀ hGcond
  have hG : G ≫ ιS = G₀ := vertexFiberLift_ι _ _ _ _
  refine { hom := F, inv := G, hom_inv_id := ?_, inv_hom_id := ?_ }
  · apply vertexFiber_hom_ext w v
    apply (cancel_mono (transportWitnessSpaceι p)).1
    simp only [Category.assoc, Category.id_comp]
    rw [← Category.assoc G ιS, hG, hG₀, hF]
  · apply vertexFiber_hom_ext q v.val
    rw [Category.assoc, hF, ← Category.assoc, hG, hG₀, Category.id_comp]

end SerrePositivity.InfinityCategories
