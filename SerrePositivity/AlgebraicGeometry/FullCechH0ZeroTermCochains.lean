module

public import SerrePositivity.AlgebraicGeometry.FullCechH0Kernel
public import SerrePositivity.AlgebraicGeometry.CechZeroTermExtension

/-!
概要：Čech H⁰ と中心の加群の組を、零次項拡張の実際のコサイクルへ写す。
方針：H⁰ と核の既存の同型の後に核の包含を合成し、中心の項では恒等を使う。
規約：基底環と加群の宇宙は独立。
使われ方：F7 の短完全列を F8 の全複体の低次数へ渡す。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory
universe u v
variable {R : Type v} [CommRing R] {ι : Type} [DecidableEq ι]

/-- 通常の Čech 複体の微分は指定したコチェイン微分。 -/
theorem fullCechComplex_d (D : Finset ι ⥤ ModuleCat.{u} R) (n : ℕ) :
    (fullCechComplex D).d n (n + 1) = ModuleCat.ofHom (fullCechDifferential D (n + 1)) := by
  exact CochainComplex.of_d
    (fun q ↦ ModuleCat.of R (FullCechCochains D (q + 1)))
    (fun q ↦ ModuleCat.ofHom (fullCechDifferential D (q + 1))) n

/-- H⁰ と中心の項の組を零次コサイクルと中心の項の組へ写す線形写像。 -/
def fullCechH0ZeroTermCochainMap (D : Finset ι ⥤ ModuleCat.{u} R) (Q : ModuleCat.{u} R) :
    ((fullCechComplex D).homology 0 × Q) →ₗ[R]
      (cechZeroTermExtension (fullCechComplex D) Q).X 0 :=
  LinearMap.prodMap
    ((LinearMap.ker (fullCechDifferential D 1)).subtype.comp (fullCechH0KernelIso D).hom.hom)
    LinearMap.id

/-- H⁰ と中心の項から実際の零次コチェインへの写像は単射。 -/
theorem fullCechH0ZeroTermCochainMap_injective
    (D : Finset ι ⥤ ModuleCat.{u} R) (Q : ModuleCat.{u} R) :
    Function.Injective (fullCechH0ZeroTermCochainMap D Q) := by
  intro x y h
  change (((fullCechH0KernelIso D).hom.hom x.1).val, x.2) =
    (((fullCechH0KernelIso D).hom.hom y.1).val, y.2) at h
  apply Prod.ext
  · apply (fullCechH0KernelIso D).toLinearEquiv.injective
    exact Subtype.ext (congrArg Prod.fst h)
  · exact congrArg (fun z : FullCechCochains D 1 × Q ↦ z.2) h

/-- 上の写像の像は零次項拡張のコサイクル。 -/
theorem fullCechH0ZeroTermCochainMap_cycle
    (D : Finset ι ⥤ ModuleCat.{u} R) (Q : ModuleCat.{u} R)
    (x : (fullCechComplex D).homology 0 × Q) :
    ((cechZeroTermExtension (fullCechComplex D) Q).d 0 1).hom
      (fullCechH0ZeroTermCochainMap D Q x) = 0 := by
  rw [cechZeroTermExtension_d]
  change ((fullCechComplex D).d 0 1).hom ((fullCechH0KernelIso D).hom.hom x.1).val = 0
  rw [fullCechComplex_d]
  exact ((fullCechH0KernelIso D).hom.hom x.1).property

/-- 零次項拡張のすべてのコサイクルは H⁰ と中心の項の組から来る。 -/
theorem fullCechH0ZeroTermCochainMap_surjective_cycles
    (D : Finset ι ⥤ ModuleCat.{u} R) (Q : ModuleCat.{u} R)
    (x : (cechZeroTermExtension (fullCechComplex D) Q).X 0)
    (hx : ((cechZeroTermExtension (fullCechComplex D) Q).d 0 1).hom x = 0) :
    ∃ y, fullCechH0ZeroTermCochainMap D Q y = x := by
  rw [cechZeroTermExtension_d] at hx
  change ((fullCechComplex D).d 0 1).hom x.1 = 0 at hx
  rw [fullCechComplex_d] at hx
  let z : LinearMap.ker (fullCechDifferential D 1) := ⟨x.1, hx⟩
  refine ⟨((fullCechH0KernelIso D).inv.hom z, x.2), ?_⟩
  apply Prod.ext
  · exact congrArg (fun b ↦ b.val) ((fullCechH0KernelIso D).toLinearEquiv.apply_symm_apply z)
  · rfl

end SerrePositivity.AlgebraicGeometry
