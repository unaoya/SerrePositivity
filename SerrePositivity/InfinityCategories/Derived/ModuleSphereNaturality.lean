module
public import SerrePositivity.InfinityCategories.Derived.MappingHomotopyGroups
/-!
概要：球面単体と Moore 境界商の実射および π の自然性。
方針：元の実射を保ち、包含・cycles・ホモロジー射の可換式を照合する。
規約：正次数は n+1。使われ方：β5(g) の単体の弱同値と準同型の比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory AlgebraicTopology Opposite
open KST.Spectra
open scoped _root_.Simplicial
variable {S : Type u} [CommRing S]
variable {W V : SimplicialObject (ModuleCat.{v} S)}
def sphericalModuleMap (f : W ⟶ V) (n : ℕ) :
    sphericalModule W n →ₗ[S] sphericalModule V n where
  toFun z := ⟨(f.app (op ⦋n + 1⦌)).hom z.val, by
    apply (Submodule.mem_iInf _).2
    intro j
    change (V.δ j).hom ((f.app (op ⦋n + 1⦌)).hom z.val) = 0
    have h := congrArg (fun ψ ↦ ψ.hom z.val) (f.naturality (SimplexCategory.δ j).op)
    change (f.app (op ⦋n⦌)).hom ((W.δ j).hom z.val) =
      (V.δ j).hom ((f.app (op ⦋n + 1⦌)).hom z.val) at h
    rw [← h]
    have hz := (Submodule.mem_iInf _).1 z.property j
    change (W.δ j).hom z.val = 0 at hz
    rw [hz, map_zero]⟩
  map_add' x y := Subtype.ext ((f.app _).hom.map_add x.val y.val)
  map_smul' r x := Subtype.ext ((f.app _).hom.map_smul r x.val)
lemma sphericalModuleMap_value (f : W ⟶ V) (n : ℕ) (z : sphericalModule W n) :
    (sphericalModuleMap f n z).val = (f.app (op ⦋n + 1⦌)).hom z.val := rfl
def mooreKernelModuleMap (f : W ⟶ V) (n : ℕ) :
    mooreKernelModule W (n + 1) →ₗ[S] mooreKernelModule V (n + 1) where
  toFun z := ⟨(f.app (op ⦋n + 1⦌)).hom z.val, by
    apply (Submodule.mem_iInf _).2
    intro j
    change (V.δ j.succ).hom ((f.app (op ⦋n + 1⦌)).hom z.val) = 0
    have h := congrArg (fun ψ ↦ ψ.hom z.val) (f.naturality (SimplexCategory.δ j.succ).op)
    change (f.app (op ⦋n⦌)).hom ((W.δ j.succ).hom z.val) =
      (V.δ j.succ).hom ((f.app (op ⦋n + 1⦌)).hom z.val) at h
    rw [← h]
    have hz := (Submodule.mem_iInf _).1 z.property j
    change (W.δ j.succ).hom z.val = 0 at hz
    rw [hz, map_zero]⟩
  map_add' x y := Subtype.ext ((f.app _).hom.map_add x.val y.val)
  map_smul' r x := Subtype.ext ((f.app _).hom.map_smul r x.val)
lemma sphericalModuleMap_boundary (f : W ⟶ V) (n : ℕ)
    (z : mooreKernelModule W (n + 2)) :
    sphericalModuleMap f n (sphereBoundaryMap W n z) =
      sphereBoundaryMap V n (mooreKernelModuleMap f (n + 1) z) := by
  apply Subtype.ext
  change (f.app (op ⦋n + 1⦌)).hom ((W.δ 0).hom z.val) =
    (V.δ 0).hom ((f.app (op ⦋n + 2⦌)).hom z.val)
  exact congrArg (fun ψ ↦ ψ.hom z.val) (f.naturality (SimplexCategory.δ 0).op)
def sphereHomologyQuotientMap (f : W ⟶ V) (n : ℕ) :
    sphereHomologyQuotient W n →ₗ[S] sphereHomologyQuotient V n :=
  Submodule.mapQ (LinearMap.range (sphereBoundaryMap W n))
    (LinearMap.range (sphereBoundaryMap V n)) (sphericalModuleMap f n) (by
      intro z hz
      obtain ⟨t, rfl⟩ := hz
      exact ⟨mooreKernelModuleMap f (n + 1) t, (sphericalModuleMap_boundary f n t).symm⟩)
lemma sphereHomologyQuotientMap_mk (f : W ⟶ V) (n : ℕ) (z : sphericalModule W n) :
    sphereHomologyQuotientMap f n (Submodule.Quotient.mk z) =
      Submodule.Quotient.mk (sphericalModuleMap f n z) := rfl
abbrev moduleUnderlyingSSetMap (f : W ⟶ V) :
    moduleUnderlyingSSet W ⟶ moduleUnderlyingSSet V :=
  Functor.whiskerRight f (forget (ModuleCat.{v} S))
lemma moduleUnderlyingSSetMap_zero (f : W ⟶ V) :
    (moduleUnderlyingSSetMap f).app (op ⦋0⦌) 0 = 0 := (f.app _).hom.map_zero
lemma pointedModuleSimplexEquiv_naturality (f : W ⟶ V) (n : ℕ)
    (s : (moduleUnderlyingSSet W).PtSimplex (n + 1) 0) :
    pointedModuleSimplexEquiv V n
      (_root_.SerrePositivity.InfinityCategories.Kan.mapSimplex (moduleUnderlyingSSetMap f) (moduleUnderlyingSSetMap_zero f) s) =
      sphericalModuleMap f n (pointedModuleSimplexEquiv W n s) := by
  apply Subtype.ext
  change SSet.yonedaEquiv (s.map ≫ moduleUnderlyingSSetMap f) = _
  rw [SSet.yonedaEquiv_comp]
  rfl
lemma modulePiSphereGroupEquiv_naturality
    [SSet.KanComplex (moduleUnderlyingSSet W)] [SSet.KanComplex (moduleUnderlyingSSet V)]
    (f : W ⟶ V) (n : ℕ) (s : _root_.SerrePositivity.InfinityCategories.Kan.KanHomotopyGroup (moduleUnderlyingSSet W) n 0) :
    modulePiSphereGroupEquiv V n
      (_root_.SerrePositivity.InfinityCategories.Kan.KanHomotopyGroup.map (n := n) (moduleUnderlyingSSetMap f)
        (moduleUnderlyingSSetMap_zero f) s) =
      sphereHomologyQuotientMap f n (modulePiSphereGroupEquiv W n s) := by
  induction s using Quotient.inductionOn with | h s =>
  change Submodule.Quotient.mk
    (pointedModuleSimplexEquiv V n
      (_root_.SerrePositivity.InfinityCategories.Kan.mapSimplex (moduleUnderlyingSSetMap f) (moduleUnderlyingSSetMap_zero f) s)) = _
  rw [pointedModuleSimplexEquiv_naturality]
  rfl
end SerrePositivity.InfinityCategories
