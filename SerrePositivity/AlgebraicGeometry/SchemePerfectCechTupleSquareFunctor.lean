module

public import SerrePositivity.AlgebraicGeometry.SchemePerfectCechTupleSquareMap

/-!
概要：同じ四角形の実際の射を、全複体の余単体図式へ渡す。
方針：四つの成分の外延性と既存の totalComplexMap の単位・合成則を使う。
規約：各項と各射に、検証済みの同じ四角形を使う。
使われ方：各項の F8 の完全性を同じ可換な二重複体へ接続する。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
universe u
variable {R S : Type u} [CommRing R] [CommRing S] {X Y : Scheme.{u}}
variable (f : X ⟶ Spec (CommRingCat.of S)) (g : Y ⟶ Spec (CommRingCat.of R))
variable (F : Arrow.mk f ⟶ Arrow.mk g) (q : R →+* S)
variable (hq : F.right = Spec.map (CommRingCat.ofHom q))
variable {ι : Type} [Fintype ι] [DecidableEq ι] (U : ι → Y.Opens)
variable (p : ℕ) (hp : p.Prime) (hR : (p : R) = 0) (hS : (p : S) = 0)

set_option backward.isDefEq.respectTransparency false in
/-- 同じ四角形の実際の射は、単位を保つ。 -/
theorem schemePerfectCechTupleSquare_map_id (n : SimplexCategory) :
    schemePerfectCechTupleSquare_map f g F q hq U p hp hR hS (𝟙 n) =
      CechAugmentedSquare.Map.id (schemePerfectCechTupleSquare f g F q hq U p hp hR hS n) := by
  apply CechAugmentedSquare.Map.ext_components
  · exact schemePerfectCechTupleMap_id g U p hp (schemeCechNervePresheaf_primeCast g p hR) n
  · exact schemePerfectCechTupleMap_id f (fun i ↦ F.left ⁻¹ᵁ U i) p hp
      (schemeCechNervePresheaf_primeCast f p hS) n
  · rfl
  · rfl

set_option backward.isDefEq.respectTransparency false in
/-- 同じ四角形の実際の射は、全ての nerve の射の合成を保つ。 -/
theorem schemePerfectCechTupleSquare_map_comp {l m n : SimplexCategory}
    (a : l ⟶ m) (b : m ⟶ n) :
    schemePerfectCechTupleSquare_map f g F q hq U p hp hR hS (a ≫ b) =
      (schemePerfectCechTupleSquare_map f g F q hq U p hp hR hS a).comp
        (schemePerfectCechTupleSquare_map f g F q hq U p hp hR hS b) := by
  apply CechAugmentedSquare.Map.ext_components
  · exact schemePerfectCechTupleMap_comp g U p hp (schemeCechNervePresheaf_primeCast g p hR) a b
  · exact schemePerfectCechTupleMap_comp f (fun i ↦ F.left ⁻¹ᵁ U i) p hp
      (schemeCechNervePresheaf_primeCast f p hS) a b
  · rfl
  · rfl

/-- 同じ四角形の全複体と実際の射を、そのまま余単体図式にまとめる。 -/
def schemePerfectCechTupleSquareFunctor :
    SimplexCategory ⥤ CochainComplex (ModuleCat.{u} ℤ) ℕ where
  obj n := (schemePerfectCechTupleSquare f g F q hq U p hp hR hS n).totalComplex
  map a := (schemePerfectCechTupleSquare_map f g F q hq U p hp hR hS a).totalComplexMap
  map_id n := by
    rw [schemePerfectCechTupleSquare_map_id, CechAugmentedSquare.Map.totalComplexMap_id]
  map_comp a b := by
    rw [schemePerfectCechTupleSquare_map_comp, CechAugmentedSquare.Map.totalComplexMap_comp]

end SerrePositivity.AlgebraicGeometry
