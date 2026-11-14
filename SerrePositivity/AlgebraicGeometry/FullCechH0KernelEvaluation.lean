module

public import SerrePositivity.AlgebraicGeometry.FullCechH0KernelNaturality

/-!
概要：Čech H⁰ と零次コサイクルの比較の自然性をタプルごとに評価する。
方針：核の包含への自然性を元とタプルで評価する。
規約：写像は既存の fullCechComplexMap が誘導する H⁰ の写像。
使われ方：順極限後の H⁰ のスカラー類と実際の増大写像の照合。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory
universe u v
variable {R : Type v} [CommRing R] {ι : Type} [DecidableEq ι]

/-- H⁰ の写像は零次コサイクルの各成分で元の係数写像に一致する。 -/
theorem fullCechH0KernelIso_naturality_apply
    {D E : Finset ι ⥤ ModuleCat.{u} R} (η : D ⟶ E)
    (a : (fullCechComplex D).homology 0) (t : Fin 1 → ι) :
    ((fullCechH0KernelIso E).hom.hom
      (((HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (.up ℕ) 0).map
        (fullCechComplexMap η)).hom a)).val t =
      (η.app (cechTupleSupport t)).hom (((fullCechH0KernelIso D).hom.hom a).val t) := by
  have h := congrArg (fun f ↦ f.hom a)
    (fullCechH0KernelIso_naturality_subtype η)
  exact congrArg (fun x ↦ x t) h

end SerrePositivity.AlgebraicGeometry
