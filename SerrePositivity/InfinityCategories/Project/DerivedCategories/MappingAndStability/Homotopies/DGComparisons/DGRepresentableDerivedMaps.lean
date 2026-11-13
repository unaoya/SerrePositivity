module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Homotopies.DGComparisons.DGNativeDerivedFiniteCell
public import SerrePositivity.DifferentialGraded.Functor.QuasiEquivalence

/-! # 代表加群間の導来射を元の閉 dg 射へ戻す

概要：代表加群間の任意の主導来射は元の dg 圏の閉次数零射の Yoneda 像で表示できる。
方針：代表加群のホモトピー射影性と全 Hom 上の Yoneda 同型を使う。
規約：dg 前三角性・元の Hom の平坦性は不要。使われ方：有限 cell roof の二射の回収。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 元の閉 dg 射の代表加群間の主導来射としての像。 -/
def dgRepresentableDerivedMap {x y : ClosedCategory A D} (f : x ⟶ y) :=
  (moduleToDerived A D).map ((dgYoneda A D).onClosed.map f)

/-- 代表加群間の導来射は元の閉 dg 射から得られる。 -/
theorem dgRepresentableDerivedMap_surjective (x y : ClosedCategory A D) :
    Function.Surjective (dgRepresentableDerivedMap A D (x := x) (y := y)) := by
  let : (dgYoneda A D).onClosed.Full :=
    (dgYoneda A D).onClosed_full_of_homIso (fun x y => by
      change IsIso (yonedaHom A D x y)
      unfold yonedaHom
      infer_instance)
  intro f
  obtain ⟨g, hg⟩ := (moduleProjectiveDerivedHomEquiv A D
    (representable_homotopicallyProjective A D x) _).surjective f
  obtain ⟨g, rfl⟩ := (moduleToHomotopy A D).map_surjective g
  obtain ⟨g, rfl⟩ := (dgYoneda A D).onClosed.map_surjective g
  rw [moduleProjectiveDerivedHomEquiv_map] at hg
  exact ⟨g, hg⟩

end SerrePositivity.InfinityCategories.Project.DerivedCategories
