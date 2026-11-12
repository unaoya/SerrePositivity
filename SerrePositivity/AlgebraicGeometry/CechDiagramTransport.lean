module

public import Mathlib.CategoryTheory.NatIso

/-!
概要：各段の複体の実際の同型を、遷移を含めた図式全体の同型にまとめる。
方針：遷移を同型で移し、単位と合成を同型の三角形で照合する。
規約：実際の切断の写像への一致は、利用側で別途示す。
使われ方：動く基底の各段の native Čech H の filtered 図式。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory
universe u v w
variable {J : Type u} [Category J] {C : Type v} [Category.{w} C]
variable (D : J ⥤ C) (Y : J → C) (e : ∀ j, D.obj j ≅ Y j)

/-- 各段の同型に沿って、図式の遷移を移す。 -/
def cechDiagramTransport : J ⥤ C where
  obj := Y
  map {i j} f := (e i).inv ≫ D.map f ≫ (e j).hom
  map_id j := by simp
  map_comp {i j k} f g := by simp [Category.assoc]

/-- 各段の同型は、移した遷移も含めた図式全体の自然同型。 -/
def cechDiagramTransportIso : D ≅ cechDiagramTransport D Y e :=
  NatIso.ofComponents e (by intro i j f; simp [cechDiagramTransport, Category.assoc])

end SerrePositivity.AlgebraicGeometry
