import SerrePositivity.HomotopicalAlgebra.Foundations
import Lean.Util.CollectAxioms

universe v u vH uH
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory HomotopicalAlgebra
open SerrePositivity SerrePositivity.HomotopyFunctionComplex

section ActualFrames
variable {C : Type u} [Category.{v} C] [ModelCategory C]

-- Ordinary model axioms supply actual morphisms above every base map.
example {X Y : FramedResolution C} (f : X.inner.base ⟶ Y.inner.base) :
    (FramedResolution.liftBase f).map.base = f := FramedResolution.liftBase_base f
example : (FramedResolution.forget (C := C)).Full := inferInstance
example : (FramedResolution.projection (C := C)).Full := inferInstance

-- Entire chains of any length retain the specified adjacent frame maps.
example {n : ℕ} (F : ComposableArrows (ResolutionObject C) n)
    (φ : ∀ i : Fin n, ResolutionLiftPrecomposition.FrameMap (FramedResolution.chainArrow F i)) :
    FramedResolution.liftChain F φ ⋙ FramedResolution.forget = F :=
  FramedResolution.liftChain_forget F φ
example (k : SimplexCategoryᵒᵖ) :
    Function.Surjective ((nerveMap (FramedResolution.forget (C := C))).app k) :=
  FramedResolution.nerveForget_surjective k
example {n m : ℕ} (F : ComposableArrows (ResolutionObject C) n)
    (φ : ∀ i : Fin n, ResolutionLiftPrecomposition.FrameMap (FramedResolution.chainArrow F i))
    (θ : SimplexCategory.mk m ⟶ SimplexCategory.mk n) :
    (θ.toOrderHom.monotone.functor ⋙ FramedResolution.liftChain F φ) ⋙ FramedResolution.forget =
      θ.toOrderHom.monotone.functor ⋙ F := FramedResolution.liftChain_reindex_forget F φ θ
end ActualFrames

section KanValues
variable {C : Type u} [Category.{v} C] [ModelCategory C] [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)

-- The source is arbitrary; the actual values remain in its original Hom universe v.
example : (FramedResolution C)ᵒᵖ ⥤ C ⥤ SSet.{v} := FramedResolution.hom hcof hfib
example (X : (FramedResolution C)ᵒᵖ) (Z : C) :
    SSet.KanComplex (((FramedResolution.hom hcof hfib).obj X).obj Z) :=
  FramedResolution.hom_kanComplex hcof hfib X Z
example {X Y : (FramedResolution C)ᵒᵖ} (f : X ⟶ Y)
    (hf : weakEquivalences C f.unop.map.base) (Z : C) [IsFibrant Z] :
    weakEquivalences SSet.{v} (((FramedResolution.hom hcof hfib).map f).app Z) :=
  FramedResolution.hom_source_weakEquivalence hcof hfib f hf Z
example (X : (FramedResolution C)ᵒᵖ) {Z Z' : C} [IsFibrant Z] [IsFibrant Z']
    (f : Z ⟶ Z') (hf : weakEquivalences C f) :
    weakEquivalences SSet.{v} (((FramedResolution.hom hcof hfib).obj X).map f) :=
  FramedResolution.hom_target_weakEquivalence hcof hfib X f hf

-- Unit, arbitrary composition, and both-variable naturality are actual functor equations.
example {n m : ℕ} (F : ComposableArrows (FramedResolution C) n)
    (θ : SimplexCategory.mk m ⟶ SimplexCategory.mk n) :
    FramedResolution.chainHom hcof hfib (θ.toOrderHom.monotone.functor ⋙ F) =
      θ.toOrderHom.monotone.functor.op ⋙ FramedResolution.chainHom hcof hfib F :=
  FramedResolution.chainHom_reindex hcof hfib F θ
example {n : ℕ} (F : ComposableArrows (FramedResolution C) n)
    {i j k : (Fin (n + 1))ᵒᵖ} (a : i ⟶ j) (b : j ⟶ k) (Z : C) :
    ((FramedResolution.chainHom hcof hfib F).map (a ≫ b)).app Z =
      ((FramedResolution.chainHom hcof hfib F).map a).app Z ≫
        ((FramedResolution.chainHom hcof hfib F).map b).app Z :=
  FramedResolution.chainHom_composition hcof hfib F a b Z

variable {H : Type uH} [Category.{vH} H]

example (Q : C ⥤ H) [Q.IsLocalization (weakEquivalences C)]
    (X : (FramedResolution C)ᵒᵖ) (Z : C) [IsFibrant Z] :
    SSet.π₀ (((FramedResolution.hom hcof hfib).obj X).obj Z) ≃
      (Q.obj X.unop.inner.base ⟶ Q.obj Z) :=
  FramedResolution.piZeroEquiv hcof hfib Q X Z

-- Choice independence is proved on full Ho(SSet) morphisms, beyond π₀.
example (L : SSet.{v} ⥤ H) [L.IsLocalization (weakEquivalences SSet.{v})] :
    FramedResolution.localizedRaw (C := C) L ≅ FramedResolution.localizedHom hcof hfib L :=
  FramedResolution.localizedComparisonIso hcof hfib L
example (L : SSet.{v} ⥤ H) [L.IsLocalization (weakEquivalences SSet.{v})]
    {X Y : (FramedResolution C)ᵒᵖ} (f g : X ⟶ Y)
    (h : f.unop.map.base = g.unop.map.base) (Z : FibrantObject C) :
    L.map (((FramedResolution.hom hcof hfib).map f).app Z.obj) =
      L.map (((FramedResolution.hom hcof hfib).map g).app Z.obj) :=
  FramedResolution.localized_map_eq_of_base_eq hcof hfib L f g h Z
end KanValues

open Lean in
run_cmd do
  let env ← getEnv
  let expected := #[
    `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FramedResolutionCategory,
    `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FramedMappingBifunctor,
    `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FramedResolutionChains,
    `SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FramedMappingLocalization]
  let mut count : Nat := 0
  let mut modules : Array Name := #[]
  for (name, _) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let mod := env.header.modules[idx.toNat]!.module
    unless expected.contains mod do continue
    let axioms ← collectAxioms name
    unless axioms.all (#[``propext, ``Classical.choice, ``Quot.sound].contains ·) do
      throwError "Unexpected axioms in {name}: {axioms}"
    count := count + 1
    unless modules.contains mod do modules := modules.push mod
  unless modules.size == expected.size do
    throwError "Some framed mapping modules were not audited"
  logInfo m!"Framed mapping bifunctor audit passed: {count} declarations \
    in {modules.size} modules, standard axioms only."
