module

public import SerrePositivity.InfinityCategories.F2.Ind.TrivialCosliceEndpointLifting

/-!
概要：射影の同じ厳密な切断を、点の coslice 上で比較する写像。
方針：端点の切断と後合成で二つの引き戻しの成分を照合する。
規約：元の点と切断の等式を保持する。使われ方：切断自体の cofinal 性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
variable {E B : SSet.{u}} (a : (Δ[0] : SSet.{u}) ⟶ E) (p : E ⟶ B) (s : B ⟶ E)

instance cosliceEndpointMap_trivialKanFibration [TrivialKanFibration p] :
    TrivialKanFibration (cosliceEndpointMap a p) := by
  apply (trivialKanFibration_iff_boundary _).mpr
  intro n
  exact cosliceEndpointMap_lifting_of_trivial a p (boundary n)

/-- 同じ切断の coslice 引き戻しから、底の元の coslice への写像。 -/
def sectionCosliceMap : pullback s (sliceUnderProjection a) ⟶ sliceUnder (a ≫ p) :=
  pullback.snd s (sliceUnderProjection a) ≫ sliceUnderPostcomp a p

/-- 同じ比較の端点は元の第一射影。 -/
lemma sectionCosliceMap_projection (hs : s ≫ p = 𝟙 B) :
    sectionCosliceMap a p s ≫ sliceUnderProjection (a ≫ p) =
      pullback.fst s (sliceUnderProjection a) := by
  have h := congrArg (fun f => f ≫ p)
    (pullback.condition (f := s) (g := sliceUnderProjection a))
  rw [Category.assoc, hs, Category.comp_id] at h
  exact h.symm

/-- 底の coslice に切断の端点を指定した元の比較対象。 -/
def sectionCosliceTarget (hs : s ≫ p = 𝟙 B) :
    sliceUnder (a ≫ p) ⟶ pullback p (sliceUnderProjection (a ≫ p)) :=
  pullback.lift (sliceUnderProjection (a ≫ p) ≫ s) (𝟙 _)
    (by rw [Category.assoc, hs, Category.comp_id, Category.id_comp])

lemma sectionCosliceTarget_fst (hs : s ≫ p = 𝟙 B) :
    sectionCosliceTarget a p s hs ≫ pullback.fst p (sliceUnderProjection (a ≫ p)) =
      sliceUnderProjection (a ≫ p) ≫ s := pullback.lift_fst _ _ _

lemma sectionCosliceTarget_snd (hs : s ≫ p = 𝟙 B) :
    sectionCosliceTarget a p s hs ≫ pullback.snd p (sliceUnderProjection (a ≫ p)) = 𝟙 _ :=
  pullback.lift_snd _ _ _

/-- 元の coslice の二つの比較は、端点を含めて厳密に可換。 -/
lemma sectionCosliceMap_endpoint (hs : s ≫ p = 𝟙 B) :
    pullback.snd s (sliceUnderProjection a) ≫ cosliceEndpointMap a p =
      sectionCosliceMap a p s ≫ sectionCosliceTarget a p s hs := by
  apply pullback.hom_ext
  · rw [Category.assoc, cosliceEndpointMap_fst, Category.assoc, sectionCosliceTarget_fst,
      ← Category.assoc, sectionCosliceMap_projection a p s hs]
    exact (pullback.condition (f := s) (g := sliceUnderProjection a)).symm
  · rw [Category.assoc, cosliceEndpointMap_snd, Category.assoc, sectionCosliceTarget_snd,
      Category.comp_id]
    rfl

end SerrePositivity.InfinityCategories.F2.Ind
