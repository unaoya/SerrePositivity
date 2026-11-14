module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.FunctorComparisons.EnrichedFunctors.ModulePiMooreNaturality
/-!
概要：実連結成分と正規化一次境界商の比較。
方針：実辺・正規化の包含・標準ホモロジー射の可換式を使う。
規約：元の正規化射を保持する。使われ方：β5(g) の弱同値の比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory AlgebraicTopology Opposite HomologicalComplex
open KST.Spectra
open scoped _root_.Simplicial
variable {S : Type u} [CommRing S]
variable (W : SimplicialObject (ModuleCat.{v} S))
def moduleZeroBoundaryMap : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.mooreKernelModule W 1 →ₗ[S] W.obj (op ⦋0⦌) :=
  (W.δ 0).hom.comp (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.mooreKernelModule W 1).subtype
abbrev moduleZeroBoundaryQuotient :=
  W.obj (op ⦋0⦌) ⧸ LinearMap.range (moduleZeroBoundaryMap W)
lemma moduleEdge_sub_mem_zeroBoundary {x y : W.obj (op ⦋0⦌)}
    (e : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleUnderlyingSSet W).Edge x y) :
    x - y ∈ LinearMap.range (moduleZeroBoundaryMap W) := by
  let t : W.obj (op ⦋1⦌) := e.edge
  let s : W.obj (op ⦋1⦌) := (W.σ 0).hom x
  have hs : (W.δ 1).hom e.edge = x := e.src_eq
  have ht : (W.δ 0).hom e.edge = y := e.tgt_eq
  have hd₁ : (W.δ (1 : Fin 2)).hom ((W.σ (0 : Fin 1)).hom x) = x :=
    congrArg (fun ψ ↦ ψ.hom x) (W.δ_comp_σ_succ (i := (0 : Fin 1)))
  have hd₀ : (W.δ (0 : Fin 2)).hom ((W.σ (0 : Fin 1)).hom x) = x :=
    congrArg (fun ψ ↦ ψ.hom x) (W.δ_comp_σ_self (i := (0 : Fin 1)))
  let z : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.mooreKernelModule W 1 := ⟨s - t, by
    apply (Submodule.mem_iInf _).2
    intro j
    fin_cases j
    change (W.δ 1).hom (s - t) = 0
    rw [map_sub, hd₁, hs, sub_self]⟩
  refine ⟨z, ?_⟩
  change (W.δ 0).hom (s - t) = x - y
  rw [map_sub, hd₀, ht]
lemma moduleZeroBoundary_exists_edge {x y : W.obj (op ⦋0⦌)}
    (h : x - y ∈ LinearMap.range (moduleZeroBoundaryMap W)) :
    Nonempty ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleUnderlyingSSet W).Edge x y) := by
  obtain ⟨z, hz⟩ := h
  have hz₁ : (W.δ (1 : Fin 2)).hom z.val = 0 :=
    (Submodule.mem_iInf _).1 z.property (0 : Fin 1)
  have hd₁ : (W.δ (1 : Fin 2)).hom ((W.σ (0 : Fin 1)).hom x) = x :=
    congrArg (fun ψ ↦ ψ.hom x) (W.δ_comp_σ_succ (i := (0 : Fin 1)))
  have hd₀ : (W.δ (0 : Fin 2)).hom ((W.σ (0 : Fin 1)).hom x) = x :=
    congrArg (fun ψ ↦ ψ.hom x) (W.δ_comp_σ_self (i := (0 : Fin 1)))
  refine ⟨SSet.Edge.mk ((W.σ 0).hom x - z.val) ?_ ?_⟩
  · change (W.δ 1).hom ((W.σ 0).hom x - z.val) = x
    rw [map_sub, hd₁, hz₁, sub_zero]
  · change (W.δ 0).hom ((W.σ 0).hom x - z.val) = y
    change (W.δ 0).hom z.val = x - y at hz
    rw [map_sub, hd₀, hz, sub_sub_cancel]
def modulePiZeroBoundaryQuotient :
    SSet.π₀ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleUnderlyingSSet W) → moduleZeroBoundaryQuotient W :=
  SSet.π₀.lift Submodule.Quotient.mk (fun _ _ e ↦
    (Submodule.Quotient.eq _).2 (moduleEdge_sub_mem_zeroBoundary W e))
lemma modulePiZeroBoundaryQuotient_mk (x : W.obj (op ⦋0⦌)) :
    modulePiZeroBoundaryQuotient W (SSet.π₀.mk x) = Submodule.Quotient.mk x := rfl
lemma modulePiZeroBoundaryQuotient_bijective :
    Function.Bijective (modulePiZeroBoundaryQuotient W) := by
  constructor
  · intro a b hab
    obtain ⟨a, rfl⟩ := SSet.π₀.mk_surjective a
    obtain ⟨b, rfl⟩ := SSet.π₀.mk_surjective b
    have h : a - b ∈ LinearMap.range (moduleZeroBoundaryMap W) :=
      (Submodule.Quotient.eq _).1 hab
    obtain ⟨e⟩ := moduleZeroBoundary_exists_edge W h
    exact SSet.π₀.sound e
  · intro z
    obtain ⟨z, rfl⟩ := Submodule.mkQ_surjective (LinearMap.range (moduleZeroBoundaryMap W)) z
    exact ⟨SSet.π₀.mk z, rfl⟩
def modulePiZeroBoundaryEquiv :
    SSet.π₀ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleUnderlyingSSet W) ≃ moduleZeroBoundaryQuotient W :=
  Equiv.ofBijective (modulePiZeroBoundaryQuotient W) (modulePiZeroBoundaryQuotient_bijective W)
variable {W} {V : SimplicialObject (ModuleCat.{v} S)}
lemma moduleZeroBoundaryMap_naturality (f : W ⟶ V) (z : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.mooreKernelModule W 1) :
    (f.app (op ⦋0⦌)).hom (moduleZeroBoundaryMap W z) =
      moduleZeroBoundaryMap V (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.mooreKernelModuleMap f 0 z) := by
  exact congrArg (fun ψ ↦ ψ.hom z.val) (f.naturality (SimplexCategory.δ 0).op)
def moduleZeroBoundaryQuotientMap (f : W ⟶ V) :
    moduleZeroBoundaryQuotient W →ₗ[S] moduleZeroBoundaryQuotient V :=
  Submodule.mapQ (LinearMap.range (moduleZeroBoundaryMap W))
    (LinearMap.range (moduleZeroBoundaryMap V)) (f.app (op ⦋0⦌)).hom (by
      intro z hz
      obtain ⟨t, rfl⟩ := hz
      exact ⟨_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.mooreKernelModuleMap f 0 t, (moduleZeroBoundaryMap_naturality f t).symm⟩)
lemma modulePiZeroBoundaryEquiv_naturality (f : W ⟶ V)
    (z : SSet.π₀ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleUnderlyingSSet W)) :
    modulePiZeroBoundaryEquiv V (SSet.mapπ₀ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleUnderlyingSSetMap f) z) =
      moduleZeroBoundaryQuotientMap f (modulePiZeroBoundaryEquiv W z) := by
  induction z using SSet.π₀.rec with | mk z => rfl
end SerrePositivity.InfinityCategories.Project.DerivedCategories
