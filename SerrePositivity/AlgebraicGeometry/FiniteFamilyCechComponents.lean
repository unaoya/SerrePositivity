module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicTopology.CechNerve

/-!
概要：同じ有限族の混合ファイバー積から、元の余積射の nerve への標準射を取る。
方針：元の各射影に同じ余積入射を合成し、wide pullback の普遍性を使う。
規約：同じ基底、各射影、単体の射による再添字付けを保つ。
使われ方：有限アフィン族と同じ矩形タプルの係数比較。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory CategoryTheory.Limits _root_.AlgebraicGeometry Opposite
universe u
variable {ι : Type} {S : Scheme.{u}} {Z : ι → Scheme.{u}} (f : ∀ i, Z i ⟶ S)

/-- 同じ族の指定された成分の、元の基底上の混合ファイバー積。 -/
abbrev finiteFamilyCechComponent (n : SimplexCategory) (t : Fin (n.len + 1) → ι) : Scheme.{u} :=
  widePullback S (fun j ↦ Z (t j)) (fun j ↦ f (t j))

/-- 同じ混合ファイバー積から元の余積射の nerve への、元の射影による標準射。 -/
def finiteFamilyCechInclusion (n : SimplexCategory) (t : Fin (n.len + 1) → ι) :
    finiteFamilyCechComponent f n t ⟶
      (Arrow.mk (CategoryTheory.Limits.Sigma.desc f)).cechNerve.obj (op n) :=
  WidePullback.lift (WidePullback.base (fun j ↦ f (t j)))
    (fun j ↦ WidePullback.π (fun j ↦ f (t j)) j ≫ Sigma.ι Z (t j))
    (fun j ↦ by
      change (WidePullback.π (fun j ↦ f (t j)) j ≫ Sigma.ι Z (t j)) ≫ Sigma.desc f = _
      rw [Category.assoc, Sigma.ι_comp_desc, WidePullback.π_arrow])

/-- 元の nerve の射影との合成は、同じ成分の射影と元の余積入射。 -/
theorem finiteFamilyCechInclusion_π (n : SimplexCategory) (t : Fin (n.len + 1) → ι)
    (j : Fin (n.len + 1)) :
    finiteFamilyCechInclusion f n t ≫
        WidePullback.π (fun _ : Fin (n.len + 1) ↦ CategoryTheory.Limits.Sigma.desc f) j =
      WidePullback.π (fun j ↦ f (t j)) j ≫ Sigma.ι Z (t j) :=
  WidePullback.lift_π _ _ _ _ j

/-- 同じ標準射は基底への射を保つ。 -/
theorem finiteFamilyCechInclusion_base (n : SimplexCategory) (t : Fin (n.len + 1) → ι) :
    finiteFamilyCechInclusion f n t ≫
        WidePullback.base (fun _ : Fin (n.len + 1) ↦ CategoryTheory.Limits.Sigma.desc f) =
      WidePullback.base (fun j ↦ f (t j)) :=
  WidePullback.lift_base _ _ _ _

/-- 単体の射による同じ成分の再添字付けを、元の射影で引き戻す。 -/
def finiteFamilyCechComponentMap {m n : SimplexCategory} (a : m ⟶ n)
    (t : Fin (n.len + 1) → ι) :
    finiteFamilyCechComponent f n t ⟶
      finiteFamilyCechComponent f m (fun j ↦ t (a.toOrderHom j)) :=
  WidePullback.lift (WidePullback.base (fun j ↦ f (t j)))
    (fun j ↦ WidePullback.π (fun j ↦ f (t j)) (a.toOrderHom j))
    (fun j ↦ WidePullback.π_arrow (fun j ↦ f (t j)) (a.toOrderHom j))

set_option backward.isDefEq.respectTransparency false in
/-- 同じ混合ファイバー積からの標準射は、元の nerve の全ての射に自然。 -/
theorem finiteFamilyCechInclusion_naturality {m n : SimplexCategory} (a : m ⟶ n)
    (t : Fin (n.len + 1) → ι) :
    finiteFamilyCechComponentMap f a t ≫
        finiteFamilyCechInclusion f m (fun j ↦ t (a.toOrderHom j)) =
      finiteFamilyCechInclusion f n t ≫
        (Arrow.mk (CategoryTheory.Limits.Sigma.desc f)).cechNerve.map a.op := by
  apply WidePullback.hom_ext
  · intro j
    change (finiteFamilyCechComponentMap f a t ≫
        finiteFamilyCechInclusion f m (fun j ↦ t (a.toOrderHom j))) ≫
        WidePullback.π (fun _ : Fin (m.len + 1) ↦ Sigma.desc f) j =
      (finiteFamilyCechInclusion f n t ≫
        (Arrow.mk (Sigma.desc f)).cechNerve.map a.op) ≫
        WidePullback.π (fun _ : Fin (m.len + 1) ↦ Sigma.desc f) j
    have ha : (Arrow.mk (Sigma.desc f)).cechNerve.map a.op ≫
        WidePullback.π (fun _ : Fin (m.len + 1) ↦ Sigma.desc f) j =
      WidePullback.π (fun _ : Fin (n.len + 1) ↦ Sigma.desc f) (a.toOrderHom j) := by
      change WidePullback.lift (WidePullback.base (fun _ : Fin (n.len + 1) ↦ Sigma.desc f))
        (fun i : Fin (m.len + 1) ↦ WidePullback.π
          (fun _ : Fin (n.len + 1) ↦ Sigma.desc f) (a.toOrderHom i)) _ ≫ _ = _
      exact WidePullback.lift_π _ _ _ _ j
    rw [Category.assoc, finiteFamilyCechInclusion_π, Category.assoc, ha,
      finiteFamilyCechInclusion_π, ← Category.assoc]
    change (WidePullback.lift _ _ _ ≫ WidePullback.π
      (fun j : Fin (m.len + 1) ↦ f (t (a.toOrderHom j))) j) ≫ _ = _
    rw [WidePullback.lift_π]
  · change (finiteFamilyCechComponentMap f a t ≫
        finiteFamilyCechInclusion f m (fun j ↦ t (a.toOrderHom j))) ≫
        WidePullback.base (fun _ : Fin (m.len + 1) ↦ Sigma.desc f) =
      (finiteFamilyCechInclusion f n t ≫
        (Arrow.mk (Sigma.desc f)).cechNerve.map a.op) ≫
        WidePullback.base (fun _ : Fin (m.len + 1) ↦ Sigma.desc f)
    have ha : (Arrow.mk (Sigma.desc f)).cechNerve.map a.op ≫
        WidePullback.base (fun _ : Fin (m.len + 1) ↦ Sigma.desc f) =
      WidePullback.base (fun _ : Fin (n.len + 1) ↦ Sigma.desc f) := by
      change WidePullback.lift (WidePullback.base (fun _ : Fin (n.len + 1) ↦ Sigma.desc f))
        (fun i : Fin (m.len + 1) ↦ WidePullback.π
          (fun _ : Fin (n.len + 1) ↦ Sigma.desc f) (a.toOrderHom i)) _ ≫ _ = _
      exact WidePullback.lift_base _ _ _ _
    rw [Category.assoc, finiteFamilyCechInclusion_base, Category.assoc, ha,
      finiteFamilyCechInclusion_base]
    exact WidePullback.lift_base _ _ _ _

/-- 同じ成分の余積から元の nerve 項への標準射。 -/
def finiteFamilyCechMap (n : SimplexCategory) :
    (∐ (fun t : Fin (n.len + 1) → ι ↦ finiteFamilyCechComponent f n t)) ⟶
      (Arrow.mk (CategoryTheory.Limits.Sigma.desc f)).cechNerve.obj (op n) :=
  Sigma.desc (finiteFamilyCechInclusion f n)

end SerrePositivity.AlgebraicGeometry
