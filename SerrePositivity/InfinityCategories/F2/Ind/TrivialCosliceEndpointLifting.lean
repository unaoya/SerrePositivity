module
public import SerrePositivity.InfinityCategories.Core.CosliceEndpointFibration
public import SerrePositivity.InfinityCategories.Core.Terminal
/-!
概要：trivial Kan 射影の相対 coslice は全ての境界を持ち上げる。
方針：既存の端点比較と同じ join の貼り合わせに、全単射に対する持ち上げを適用する。
規約：元の図式と端点を厳密に保つ。使われ方：同じ射影の切断の cofinal 性。
-/
@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
lemma cosliceEndpointMap_lifting_of_trivial {A K E B : SSet.{u}}
    (a : K ⟶ E) (p : E ⟶ B) [TrivialKanFibration p]
    (A₀ : A.Subcomplex) :
    HasLiftingProperty A₀.ι (cosliceEndpointMap a p) := by
  constructor
  intro u b sq
  let Z : SSet.{u} := (⊥ : K.Subcomplex)
  let G := sliceUnderUncurry u
  let H := (emptyJoinIso K A).hom ≫ b ≫ pullback.fst p (sliceUnderProjection (a ≫ p))
  let F := sliceUnderUncurry (b ≫ pullback.snd p (sliceUnderProjection (a ≫ p)))
  have hfirst : u ≫ sliceUnderProjection a =
      A₀.ι ≫ b ≫ pullback.fst p (sliceUnderProjection (a ≫ p)) := by
    have hh := congrArg (fun t ↦ t ≫ pullback.fst p (sliceUnderProjection (a ≫ p))) sq.w
    simpa only [Category.assoc, cosliceEndpointMap_fst] using hh
  have hsecond : G ≫ p = joinMap (𝟙 K) A₀.ι ≫ F := by
    have hh := congrArg (fun t ↦ t ≫ pullback.snd p (sliceUnderProjection (a ≫ p))) sq.w
    simp only [Category.assoc, cosliceEndpointMap_snd] at hh
    have hu := congrArg sliceUnderUncurry hh
    rw [sliceUnderUncurry_postcomp, sliceUnderUncurry_precomp] at hu
    exact hu
  have hover : joinMap (⊥ : K.Subcomplex).ι (𝟙 (A₀ : SSet.{u})) ≫ G =
      joinMap (𝟙 Z) A₀.ι ≫ H := by
    apply (cancel_epi (emptyJoinIso K (A₀ : SSet.{u})).inv).1
    rw [← Category.assoc, emptyJoinIso_inv, joinInr_joinMap, Category.id_comp,
      ← Category.assoc, joinInr_joinMap, Category.assoc]
    change joinInr K (A₀ : SSet.{u}) ≫ G =
      A₀.ι ≫ ((emptyJoinIso K A).inv ≫ ((emptyJoinIso K A).hom ≫
        b ≫ pullback.fst p (sliceUnderProjection (a ≫ p))))
    rw [Iso.inv_hom_id_assoc, sliceUnderUncurry_projection]
    exact hfirst
  let hs := (joinUnion_isPushout (⊥ : K.Subcomplex) A₀).flip
  let T := hs.desc G H hover
  have hH : H ≫ p = joinMap (⊥ : K.Subcomplex).ι (𝟙 A) ≫ F := by
    apply (cancel_epi (emptyJoinIso K A).inv).1
    simp only [H, Category.assoc, Iso.inv_hom_id_assoc]
    rw [← Category.assoc (emptyJoinIso K A).inv, emptyJoinIso_inv, joinInr_joinMap,
      Category.id_comp, pullback.condition]
    simpa only [Category.assoc] using (sliceUnderUncurry_projection
      (b ≫ pullback.snd p (sliceUnderProjection (a ≫ p)))).symm
  have hT : CommSq T (joinUnion (⊥ : K.Subcomplex) A₀).ι p F := by
    constructor
    apply hs.hom_ext
    · rw [← Category.assoc, hs.inl_desc, reassoc_of% joinUnionRight_ι]
      exact hsecond
    · rw [← Category.assoc, hs.inr_desc, reassoc_of% joinUnionLeft_ι]
      exact hH
  have := TrivialKanFibration.mem (p := p) (joinUnion (⊥ : K.Subcomplex) A₀).ι inferInstance
  let L := hT.lift
  have hleft : joinMap (𝟙 K) A₀.ι ≫ L = G := by
    rw [← joinUnionRight_ι, Category.assoc, hT.fac_left]
    exact hs.inl_desc _ _ _
  have hright : joinMap (⊥ : K.Subcomplex).ι (𝟙 A) ≫ L = H := by
    rw [← joinUnionLeft_ι, Category.assoc, hT.fac_left]
    exact hs.inr_desc _ _ _
  have hfixed : joinInl K A ≫ L = a := by
    have hh := congrArg (fun z ↦ joinInl K (A₀ : SSet.{u}) ≫ z) hleft
    rw [← Category.assoc, joinInl_joinMap, Category.id_comp] at hh
    exact hh.trans (sliceUnderUncurry_fixed u)
  refine CommSq.HasLift.mk' { l := sliceUnderCurry L hfixed, fac_left := ?_, fac_right := ?_ }
  · apply sliceUnderUncurry_injective a
    rw [sliceUnderUncurry_precomp, sliceUnderUncurry_curry]
    exact hleft
  · apply pullback.hom_ext
    · rw [Category.assoc, cosliceEndpointMap_fst, sliceUnderCurry_projection]
      have hh := congrArg (fun z ↦ (emptyJoinIso K A).inv ≫ z) hright
      rw [← Category.assoc, emptyJoinIso_inv, joinInr_joinMap, Category.id_comp] at hh
      exact hh.trans (by dsimp [H]; rw [← emptyJoinIso_inv, Iso.inv_hom_id_assoc])
    · rw [Category.assoc, cosliceEndpointMap_snd]
      apply sliceUnderUncurry_injective (a ≫ p)
      rw [sliceUnderUncurry_postcomp, sliceUnderUncurry_curry]
      exact hT.fac_right
end SerrePositivity.InfinityCategories.F2.Ind
