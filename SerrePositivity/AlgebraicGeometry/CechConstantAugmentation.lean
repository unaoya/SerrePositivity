module

public import SerrePositivity.AlgebraicGeometry.ProjectiveCechComplex

/-!
概要：同じ空集合の係数から、全タプル余単体図式への増大を全次数で保つ。
方針：空集合から各タプルの有限像への元の制限写像を使う。
規約：同じ係数・有限像・再添字付けを保持する。
使われ方：平坦な二重 Čech の行の増大と、零次 single の比較。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory
universe u v
variable {R : Type v} [CommRing R] {ι : Type} [DecidableEq ι]
variable (D : Finset ι ⥤ ModuleCat.{u} R)

/-- 同じ空集合の係数から、全てのタプルの有限像への制限による増大。 -/
def fullCechConstantAugmentation :
    (Functor.const SimplexCategory).obj (D.obj ∅) ⟶ fullCechCosimplicial D where
  app n := ModuleCat.ofHom (LinearMap.pi (fun t : Fin (n.len + 1) → ι ↦
    (D.map (homOfLE (Finset.empty_subset (cechTupleSupport t)))).hom))
  naturality {m n} a := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    funext t
    change (D.map (homOfLE (Finset.empty_subset (cechTupleSupport t)))).hom x =
      (D.map (homOfLE (cechTupleSupport_comp_subset t a.toOrderHom))).hom
        ((D.map (homOfLE (Finset.empty_subset (cechTupleSupport (t ∘ a.toOrderHom))))).hom x)
    rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, ← D.map_comp]
    rfl

/-- 同じ全次数の増大の評価は、元の有限像への制限。 -/
theorem fullCechConstantAugmentation_apply (n : SimplexCategory) (x : D.obj ∅)
    (t : Fin (n.len + 1) → ι) :
    ((fullCechConstantAugmentation D).app n).hom x t =
      (D.map (homOfLE (Finset.empty_subset (cechTupleSupport t)))).hom x := rfl

end SerrePositivity.AlgebraicGeometry
