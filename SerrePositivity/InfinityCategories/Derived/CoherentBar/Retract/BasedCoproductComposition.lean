module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.Retract.BasedCoproduct
/-!
概要：未シフト係数直和の始点保存作用が単体写像の合成を保つことを示す。
方針：三つの対象輸送の型を先に固定し、直和包含への制限で比較する。
規約：作用の合成は厳密な等式であり、ホモトピー圏への移送で代用しない。
使われ方：同じ係数直和にラベルの正規化作用を移す。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded DGNerve SSet
open scoped Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  {I : SSet.{u}}
  (F : (SSet.uliftFunctor.{max (u + 1) v, u}).obj I ⟶ dgNerve R (RightModule R D))

private lemma inclusion_paths {n : ℕ} {s t : I _⦋n⦌} (h : s = t)
    (M : ModuleCategory R D) (hs : M = dgCoherentBarBasedFamily R D F n s)
    (ht : M = dgCoherentBarBasedFamily R D F n t) :
    eqToHom hs ≫ Sigma.ι (dgCoherentBarBasedFamily R D F n) s =
      eqToHom ht ≫ Sigma.ι (dgCoherentBarBasedFamily R D F n) t := by
  cases h
  rfl

lemma dgCoherentBarBasedMap_comp {l m n : ℕ}
    (f : ⦋m⦌ ⟶ ⦋n⦌) (hf : f.toOrderHom 0 = 0)
    (g : ⦋l⦌ ⟶ ⦋m⦌) (hg : g.toOrderHom 0 = 0) :
    dgCoherentBarBasedMap R D F f hf ≫ dgCoherentBarBasedMap R D F g hg =
      dgCoherentBarBasedMap R D F (g ≫ f) (by
        change f.toOrderHom (g.toOrderHom 0) = 0
        rw [hg, hf]) := by
  apply Sigma.hom_ext
  intro s
  have hi : I.map g.op (I.map f.op s) = I.map (g ≫ f).op s := by
    exact (ConcreteCategory.congr_hom (I.map_comp f.op g.op) s).symm
  let h₁ : dgCoherentBarBasedFamily R D F n s =
      dgCoherentBarBasedFamily R D F m (I.map f.op s) :=
    (congrArg (ForgetEnrichment.of (Complex R))
      (dgCoherentBarSource_based_map R D F f hf s)).symm
  let h₂ : dgCoherentBarBasedFamily R D F m (I.map f.op s) =
      dgCoherentBarBasedFamily R D F l (I.map g.op (I.map f.op s)) :=
    (congrArg (ForgetEnrichment.of (Complex R))
      (dgCoherentBarSource_based_map R D F g hg (I.map f.op s))).symm
  let h₃ : dgCoherentBarBasedFamily R D F n s =
      dgCoherentBarBasedFamily R D F l (I.map (g ≫ f).op s) :=
    (congrArg (ForgetEnrichment.of (Complex R))
      (dgCoherentBarSource_based_map R D F (g ≫ f) (by
        change f.toOrderHom (g.toOrderHom 0) = 0
        rw [hg, hf]) s)).symm
  have ht := inclusion_paths R D F hi (dgCoherentBarBasedFamily R D F n s)
    (h₁.trans h₂) h₃
  have ht' : eqToHom h₁ ≫ eqToHom h₂ ≫
      Sigma.ι (dgCoherentBarBasedFamily R D F l) (I.map g.op (I.map f.op s)) =
      eqToHom h₃ ≫ Sigma.ι (dgCoherentBarBasedFamily R D F l) (I.map (g ≫ f).op s) := by
    simpa only [eqToHom_trans_assoc] using ht
  rw [dgCoherentBarBasedMap_ι_assoc, dgCoherentBarBasedMap_ι,
    dgCoherentBarBasedMap_ι]
  exact ht'

end SerrePositivity.InfinityCategories
