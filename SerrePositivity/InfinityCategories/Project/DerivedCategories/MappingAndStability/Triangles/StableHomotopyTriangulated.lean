module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.FiberCofiber.StandardConeTriangleDistinguished
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.FiberCofiber.StandardCofiberTrianglePresentation

/-! # D3 は実 cofiber による三角構造を保存する

概要：安定 D(S) の通常の h から導来圏への D3 は三角関手。
方針：全 distinguished triangle を標準 cofiber 三角形で表し、像の同型で保存を移す。
規約：始域の三角構造とシフトは安定性からのもの。使われ方：D7 の三角同値。
-/
@[expose] public section
noncomputable section
universe u w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Pretriangulated
variable (S : Type u) [CommRing S] [HasDerivedCategory.{w} (ModuleCat.{u} S)]

/-- D3 は実際の cofiber 列からの全 distinguished triangle を保存する。 -/
instance derivedStableHomotopyEquivalenceFunctorIsTriangulated :
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedStableHomotopyEquivalence S).functor.IsTriangulated where
  map_distinguished T hT := by
    obtain ⟨X, Y, f, ⟨e⟩⟩ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedDistinguishedTriangle_standard_presentation T hT
    exact isomorphic_distinguished _ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedStandardCofiberTriangle_distinguished f) _
      ((_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedStableHomotopyEquivalence S).functor.mapTriangle.mapIso e)

/-- D3 の像が distinguished であることは、元の三角形の distinguished 性と同値。 -/
lemma derivedStableHomotopyEquivalence_map_distinguished_iff
    (T : Triangle (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedStableHomotopyCategory S)) :
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedStableHomotopyEquivalence S).functor.mapTriangle.obj T ∈
        distTriang (DerivedCategory (ModuleCat S)) ↔ T ∈ distTriang _ :=
  (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedStableHomotopyEquivalence S).functor.map_distinguished_iff T

end SerrePositivity.InfinityCategories.Project.DerivedCategories
