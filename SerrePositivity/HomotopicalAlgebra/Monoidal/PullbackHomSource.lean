module

public import SerrePositivity.HomotopicalAlgebra.Monoidal.QuillenBifunctor
public import Mathlib.AlgebraicTopology.ModelCategory.BrownLemma

/-! # Source invariance of a Quillen pullback-hom at a fibrant target

The terminal pullback-hom square identifies source trivial cofibrations
with trivial fibrations. Brown factorization then gives preservation of
weak equivalences between cofibrant source objects, without a simplicial
enrichment or functorial factorizations.
-/

@[expose] public section
universe v₁ u₁ v₂ u₂ v₃ u₃
noncomputable section
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra

namespace SerrePositivity.Quillen
variable {C₁ : Type u₁} [Category.{v₁} C₁] [ModelCategory C₁]
  {C₂ : Type u₂} [Category.{v₂} C₂] [ModelCategory C₂]
  {C₃ : Type u₃} [Category.{v₃} C₃] [ModelCategory C₃]
  {F : C₁ ⥤ C₂ ⥤ C₃} {G : C₁ᵒᵖ ⥤ C₃ ⥤ C₂}
  (adj : F ⊣₂ G) [HasQuillenPullbackHom G]

include adj in
lemma pullbackHom_source_trivialFibration {A B : C₁} (i : A ⟶ B)
    [Cofibration i] [WeakEquivalence i] (Y : C₃) [IsFibrant Y] :
    trivialFibrations C₂ ((G.map i.op).app Y) := by
  have : (G.obj (Opposite.op A)).IsRightAdjoint := (adj.adj A).isRightAdjoint
  have : (G.obj (Opposite.op B)).IsRightAdjoint := (adj.adj B).isRightAdjoint
  let sq := Functor.PullbackObjObj.ofIsTerminal G i (terminal.from Y) terminalIsTerminal
  have hf := HasQuillenPullbackHom.fibration i (terminal.from Y) sq inferInstance inferInstance
  have hw := HasQuillenPullbackHom.weakEquivalence i (terminal.from Y) sq
    inferInstance inferInstance (Or.inl inferInstance)
  exact ⟨(fibration_iff _).mp hf, (weakEquivalence_iff _).mp hw⟩

include adj in
lemma pullbackHom_source_weakEquivalence {A B : C₁} [IsCofibrant A] [IsCofibrant B]
    (f : A ⟶ B) (hf : weakEquivalences C₁ f) (Y : C₃) [IsFibrant Y] :
    weakEquivalences C₂ ((G.map f.op).app Y) := by
  have : WeakEquivalence f := ⟨hf⟩
  let d := Classical.choice (inferInstance : Nonempty (CofibrantBrownFactorization f))
  have : Cofibration d.i := ⟨d.hi⟩
  have hi := (pullbackHom_source_trivialFibration adj d.i Y).2
  have hs := (pullbackHom_source_trivialFibration adj d.s Y).2
  let H := G.flip.obj Y
  have he : H.map d.p.op ≫ H.map d.s.op = 𝟙 _ := by
    rw [← H.map_comp]
    change H.map (Quiver.Hom.op (d.s ≫ d.p)) = _
    rw [d.s_p]
    exact H.map_id _
  have hp : weakEquivalences C₂ (H.map d.p.op) :=
    (weakEquivalences C₂).of_postcomp _ _ hs
      (he.symm ▸ (weakEquivalences C₂).id_mem _)
  have hfac : H.map d.p.op ≫ H.map d.i.op = H.map f.op := by
    rw [← H.map_comp]
    exact congrArg H.map (congrArg Quiver.Hom.op d.fac)
  have res := hfac ▸ (weakEquivalences C₂).comp_mem _ _ hp hi
  exact res

end SerrePositivity.Quillen
