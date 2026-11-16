module

public import SerrePositivity.AlgebraicGeometry.AffineGammaCechComponent

/-!
概要：同じアフィン nerve の Γ の標準比較は、元の全ての次数の射と増大を保つ。
方針：元の各射影と head で、同じ二つの環準同型を照合する。
規約：各次数の同型を独立に選ばず、同じ標準比較を自然にまとめる。
使われ方：環の conerve と同じアフィンの係数図式との自然な比較。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory CategoryTheory.Limits _root_.AlgebraicGeometry Opposite
universe u
variable {Y S : Scheme.{u}} (f : Y ⟶ S) [IsAffine Y] [IsAffine S]

set_option backward.isDefEq.respectTransparency false in
/-- 同じ各次数の標準比較は、元の nerve の全ての射に自然。 -/
theorem affineGammaCechComponentIso_naturality {n m : SimplexCategory} (a : n ⟶ m) :
    (Arrow.mk (Scheme.Γ.map f.op)).cechConerve.map a ≫
        (affineGammaCechComponentIso f m).hom =
      (affineGammaCechComponentIso f n).hom ≫
        ((Arrow.mk f).cechNerve.rightOp ⋙ Scheme.Γ).map a := by
  apply WidePushout.hom_ext
  · intro i
    rw [← Category.assoc, Arrow.cechConerve_map, WidePushout.ι_desc]
    change WidePushout.ι (fun _ : Fin (m.len + 1) ↦ Scheme.Γ.map f.op)
        (a.toOrderHom i) ≫ (affineGammaCechComponentIso f m).hom =
      WidePushout.ι (fun _ : Fin (n.len + 1) ↦ Scheme.Γ.map f.op) i ≫
        (affineGammaCechComponentIso f n).hom ≫
          ((Arrow.mk f).cechNerve.rightOp ⋙ Scheme.Γ).map a
    rw [affineGammaCechComponentIso_ι]
    rw [← Category.assoc, affineGammaCechComponentIso_ι]
    change Scheme.Γ.map (WidePullback.π (fun _ : Fin (m.len + 1) ↦ f)
        (a.toOrderHom i)).op =
      Scheme.Γ.map (WidePullback.π (fun _ : Fin (n.len + 1) ↦ f) i).op ≫
        Scheme.Γ.map ((Arrow.mk f).cechNerve.map a.op).op
    rw [← Scheme.Γ.map_comp]
    have h : (Arrow.mk f).cechNerve.map a.op ≫
        WidePullback.π (fun _ : Fin (n.len + 1) ↦ f) i =
      WidePullback.π (fun _ : Fin (m.len + 1) ↦ f) (a.toOrderHom i) := by
      change WidePullback.lift (WidePullback.base (fun _ : Fin (m.len + 1) ↦ f))
        (fun j : Fin (n.len + 1) ↦ WidePullback.π
          (fun _ : Fin (m.len + 1) ↦ f) (a.toOrderHom j)) _ ≫
          WidePullback.π (fun _ : Fin (n.len + 1) ↦ f) i = _
      exact WidePullback.lift_π (fun _ : Fin (n.len + 1) ↦ f) _ _ _ i
    rw [← CategoryTheory.op_comp, h]
  · rw [← Category.assoc, Arrow.cechConerve_map, WidePushout.head_desc]
    change WidePushout.head (fun _ : Fin (m.len + 1) ↦ Scheme.Γ.map f.op) ≫
        (affineGammaCechComponentIso f m).hom =
      WidePushout.head (fun _ : Fin (n.len + 1) ↦ Scheme.Γ.map f.op) ≫
        (affineGammaCechComponentIso f n).hom ≫
          ((Arrow.mk f).cechNerve.rightOp ⋙ Scheme.Γ).map a
    rw [affineGammaCechComponentIso_head]
    rw [← Category.assoc, affineGammaCechComponentIso_head]
    change Scheme.Γ.map (WidePullback.base (fun _ : Fin (m.len + 1) ↦ f)).op =
      Scheme.Γ.map (WidePullback.base (fun _ : Fin (n.len + 1) ↦ f)).op ≫
        Scheme.Γ.map ((Arrow.mk f).cechNerve.map a.op).op
    rw [← Scheme.Γ.map_comp]
    have h : (Arrow.mk f).cechNerve.map a.op ≫
        WidePullback.base (fun _ : Fin (n.len + 1) ↦ f) =
      WidePullback.base (fun _ : Fin (m.len + 1) ↦ f) := by
      change WidePullback.lift (WidePullback.base (fun _ : Fin (m.len + 1) ↦ f))
        (fun j : Fin (n.len + 1) ↦ WidePullback.π
          (fun _ : Fin (m.len + 1) ↦ f) (a.toOrderHom j)) _ ≫
          WidePullback.base (fun _ : Fin (n.len + 1) ↦ f) = _
      exact WidePullback.lift_base (fun _ : Fin (n.len + 1) ↦ f) _ _ _
    rw [← CategoryTheory.op_comp, h]

/-- 同じアフィン nerve の Γ と環の conerve の、元の全ての射を保つ標準自然同型。 -/
def affineGammaCechConerveIso : (Arrow.mk (Scheme.Γ.map f.op)).cechConerve ≅
    (Arrow.mk f).cechNerve.rightOp ⋙ Scheme.Γ :=
  NatIso.ofComponents (affineGammaCechComponentIso f)
    (fun a ↦ affineGammaCechComponentIso_naturality f a)

/-- 同じ標準自然同型は、基底からの増大写像も元の基底への射の Γ へ移す。 -/
theorem affineGammaCechConerveIso_augmentation (n : SimplexCategory) :
    (Arrow.mk (Scheme.Γ.map f.op)).augmentedCechConerve.hom.app n ≫
        (affineGammaCechConerveIso f).hom.app n =
      Scheme.Γ.map ((Arrow.mk f).augmentedCechNerve.hom.app (op n)).op :=
  affineGammaCechComponentIso_head f n

end SerrePositivity.AlgebraicGeometry
