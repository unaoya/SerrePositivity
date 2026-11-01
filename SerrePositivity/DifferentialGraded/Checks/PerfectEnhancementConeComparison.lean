module
public import SerrePositivity.DifferentialGraded.Perfect.EnhancementOperations
public import SerrePositivity.DifferentialGraded.Category.Examples
public import Mathlib.Data.ZMod.Basic

/-! # 実際のdg cone三角形の主導来比較とdistinguished性 -/
@[expose] public section
noncomputable section
universe u v
open CategoryTheory Pretriangulated
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

example (S : Set D) (M N : PerfectDGModuleOver A D S)
    (f : ForgetEnrichment.of (Complex A) M.val ⟶ ForgetEnrichment.of (Complex A) N.val) :
    perfectDGModuleConeTriangle A D S M N f ∈ distTriang (PerfectDGHomotopyCategoryOver A D S) :=
  perfectDGModuleConeTriangle_distinguished A D S M N f
example (S : Set D) (M N : PerfectDGModuleOver A D S)
    (f : ForgetEnrichment.of (Complex A) M.val ⟶ ForgetEnrichment.of (Complex A) N.val) :
    Nonempty ((perfectDGModuleToDerived A D S).mapTriangle.obj
      (perfectDGModuleConeTriangle A D S M N f) ≅ moduleDerivedConeTriangle A D f) :=
  ⟨perfectDGModuleConeTriangleToDerivedIso A D S M N f⟩
example (S : Set D) (M N : PerfectDGModuleOver A D S)
    (f : ForgetEnrichment.of (Complex A) M.val ⟶ ForgetEnrichment.of (Complex A) N.val) :
    (perfectDGModuleConeTriangle A D S M N f).mor₂ ≫
      (perfectDGModuleConeTriangle A D S M N f).mor₃ = 0 :=
  comp_distTriang_mor_zero₂₃ _ (perfectDGModuleConeTriangle_distinguished A D S M N f)
example : perfectDGModuleConeTriangle (ZMod 2) PUnit.{1} ∅
    (perfectDGModuleZero (ZMod 2) PUnit.{1} ∅) (perfectDGModuleZero (ZMod 2) PUnit.{1} ∅) 0 ∈
      distTriang (PerfectDGHomotopyCategoryOver (ZMod 2) PUnit.{1} ∅) :=
  perfectDGModuleConeTriangle_distinguished (ZMod 2) PUnit.{1} ∅ _ _ 0

#print axioms triangleComparison_mor₃
#print axioms perfectDGModuleConeTriangle_mor₃
#print axioms perfectDGModuleConeTriangle_map_mor₃
#print axioms perfectDGModuleConeConnecting_toDerived
#print axioms perfectDGModuleConeTriangle_toDerived_mor₃
#print axioms perfectDGModuleConeTriangleToDerivedIso
#print axioms perfectDGModuleConeTriangle_distinguished

#print axioms perfectDGModuleHomotopyMap_onClosed
#print axioms perfectDGHomotopy_distinguished_iff_cone
