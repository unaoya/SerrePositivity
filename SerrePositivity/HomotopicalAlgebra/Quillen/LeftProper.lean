module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.HomotopicalAlgebra.Under.Quillen
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-! # Gluing pushouts in a left proper model category

Left properness is the existing Mathlib relative cobase-change condition
on the original weak equivalivalences and cofibrations. The fixed-base
part uses the model under category and needs no properness hypothesis.
-/

@[expose] public section
universe v u
noncomputable section
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra

namespace SerrePositivity.Quillen
variable {C : Type u} [Category.{v} C] [ModelCategory C]
  [(weakEquivalences C).IsStableUnderCobaseChangeAgainst (cofibrations C)]

lemma weakEquivalence_of_pushout_along_cofibration
    {A B D P : C} {i : A ⟶ B} {f : A ⟶ D} {j : B ⟶ P} {g : D ⟶ P}
    (sq : IsPushout i f j g) (hi : cofibrations C i) (hf : weakEquivalences C f) :
    weakEquivalences C j := by
  have : (weakEquivalences C).IsStableUnderCobaseChangeAlong i :=
    MorphismProperty.IsStableUnderCobaseChangeAgainst.isStableUnderCobaseChangeAlong i hi
  exact MorphismProperty.IsStableUnderCobaseChangeAlong.of_isPushout sq hf

/-- A cube of pointwise weak equivalences induces a weak equivalence on
pushouts when the same leg in both spans is a cofibration. -/
lemma pushout_map_weakEquivalence
    {A B D A' B' D' : C} (f : A ⟶ B) (g : A ⟶ D) (f' : A' ⟶ B') (g' : A' ⟶ D')
    (a : A ⟶ A') (b : B ⟶ B') (c : D ⟶ D')
    (hf : cofibrations C f) (hf' : cofibrations C f')
    (ha : weakEquivalences C a) (hb : weakEquivalences C b) (hc : weakEquivalences C c)
    (ef : f ≫ b = a ≫ f') (eg : g ≫ c = a ≫ g') :
    weakEquivalences C (pushout.map f g f' g' b c a ef eg) := by
  let U := pushout f a
  let k : A' ⟶ U := pushout.inr f a
  let u : U ⟶ B' := pushout.desc b f' ef
  have hj : weakEquivalences C (pushout.inl f a) :=
    weakEquivalence_of_pushout_along_cofibration (IsPushout.of_hasPushout f a) hf ha
  have hu : weakEquivalences C u :=
    (weakEquivalences C).of_precomp _ _ hj (by simpa only [u, pushout.inl_desc] using hb)
  have hk : cofibrations C k :=
    (cofibrations C).of_isPushout (IsPushout.of_hasPushout f a).flip hf
  let v : Under.mk k ⟶ Under.mk f' := Under.homMk u (by simp [k, u])
  let q := ((Under.pushout g').map v).right
  have hq : weakEquivalences C q := UnderModel.pushout_map_weakEquivalence g' v hk hf' hu
  let W := pushout k g'
  let l : B ⟶ W := pushout.inl f a ≫ pushout.inl k g'
  let m : D' ⟶ W := pushout.inr k g'
  have hw : IsPushout f (a ≫ g') l m :=
    (IsPushout.of_hasPushout f a).paste_vert (IsPushout.of_hasPushout k g')
  have hw' : IsPushout f (g ≫ c) l m := eg.symm ▸ hw
  let p : pushout f g ⟶ W :=
    pushout.desc l (c ≫ m) (hw'.w.trans (Category.assoc g c m))
  have hp : IsPushout (pushout.inr f g) c p m := by
    have houter : IsPushout (g ≫ c) f m (pushout.inl f g ≫ p) := by
      simpa only [p, pushout.inl_desc] using hw'.flip
    exact (houter.of_left (by simp only [p, pushout.inr_desc])
      (IsPushout.of_hasPushout f g).flip).flip
  have hi : cofibrations C (pushout.inr f g) :=
    (cofibrations C).of_isPushout (IsPushout.of_hasPushout f g).flip hf
  have hpw : weakEquivalences C p := weakEquivalence_of_pushout_along_cofibration hp hi hc
  have hp₁ : pushout.inl f g ≫ p = l := pushout.inl_desc _ _ _
  have hp₂ : pushout.inr f g ≫ p = c ≫ m := pushout.inr_desc _ _ _
  have hq₁ : pushout.inl k g' ≫ q = u ≫ pushout.inl f' g' := pushout.inl_desc _ _ _
  have hq₂ : pushout.inr k g' ≫ q = pushout.inr f' g' := pushout.inr_desc _ _ _
  have hm₁ : pushout.inl f g ≫ pushout.map f g f' g' b c a ef eg =
      b ≫ pushout.inl f' g' := pushout.inl_desc _ _ _
  have hm₂ : pushout.inr f g ≫ pushout.map f g f' g' b c a ef eg =
      c ≫ pushout.inr f' g' := pushout.inr_desc _ _ _
  have he : p ≫ q = pushout.map f g f' g' b c a ef eg := by
    apply pushout.hom_ext
    · exact (Category.assoc _ _ _).symm.trans
        ((congrArg (fun t => t ≫ q) hp₁).trans
          ((Category.assoc _ _ _).trans
            ((congrArg (fun t => pushout.inl f a ≫ t) hq₁).trans
              ((Category.assoc _ _ _).symm.trans
                ((congrArg (fun t => t ≫ pushout.inl f' g')
                  (pushout.inl_desc b f' ef)).trans hm₁.symm)))))
    · exact (Category.assoc _ _ _).symm.trans
        ((congrArg (fun t => t ≫ q) hp₂).trans
          ((Category.assoc _ _ _).trans
            ((congrArg (fun t => c ≫ t) hq₂).trans hm₂.symm)))
  exact he ▸ (weakEquivalences C).comp_mem _ _ hpw hq

end SerrePositivity.Quillen

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HTT "A.2.4.3" (partial := stronger-hyp) "仮定：抽象モデル圏 C、元の pushout、i cofibration、j weak equivalence に加え C が左固有（Lean が強い。A,A′ の cofibrant 性は不要）。結論：同じ pushout map j′ が弱同値（一致）。一般の C で cofibrant A,A′ だけからの型はない。"] _root_.SerrePositivity.Quillen.weakEquivalence_of_pushout_along_cofibration
