module
public import SerrePositivity.KST.Fibration.StableHomCompositionVertices
public import SerrePositivity.KST.Fibration.CoherentTrianglePaths
public import SerrePositivity.KST.Fibration.ZeroStableHomComparison

/-! # 指定した零中間頂点の coherent 二単体を、元の全 Hom の零値族へ読む -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SimplicialThickening MonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration
variable (s : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u} _⦋2⦌) (hZ : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.IsZeroCategory (s.obj ⟨ULift.up 1⟩))
include hZ

/-- 元の二単体の合成 path は、途中の同じ零圏を通る完全関手を表す。 -/
theorem stableTriangleFullPath_zero :
    StableHomZeroVertex (s.obj ⟨ULift.up 0⟩) (s.obj ⟨ULift.up 2⟩)
      (coherentTriangleHomVertex s coherentTriangleFullPath) := by
  have h := stableHomZeroVertex_comp_throughZero hZ
    (coherentTriangleHomVertex s coherentTriangleFirstPath)
    (coherentTriangleHomVertex s coherentTriangleLastPath)
  exact (coherentTriangleHomVertex_comp s
    coherentTriangleFirstPath coherentTriangleLastPath).symm ▸ h

/-- 指定した二単体の全長 Hom の各頂点は、元の実零値関手を表す。 -/
theorem stableTriangleLongHom_zero :
    ∀ v, StableHomZeroVertex (s.obj ⟨ULift.up 0⟩) (s.obj ⟨ULift.up 2⟩)
      ((coherentTriangleLongHom s).app (Opposite.op ⦋0⦌) v) := by
  intro v
  obtain ⟨p, rfl⟩ := nerveEquiv.symm.surjective v
  exact (stableHomZeroVertex_iff_of_edge
    (coherentTriangleHomEdge s (coherentTrianglePathToFull p))).mpr
      (stableTriangleFullPath_zero s hZ)

/-- 元の二単体の同じ全長 Hom を、零値完全関手の実部分複体へ持ち上げる。 -/
def stableTriangleZeroHomLift :
    nerve (SimplicialThickening.Path
      (ULift.up (0 : Fin 3) : ULift.{u} (Fin 3)) (ULift.up 2)) ⟶
      zeroFunctorLocus (s.obj ⟨ULift.up 0⟩) (s.obj ⟨ULift.up 2⟩) :=
  zeroStableHomFamilyLift (coherentTriangleLongHom s) (stableTriangleLongHom_zero s hZ)

/-- 元の Kan Hom へ戻すと、指定した二単体の全長 Hom を厳密に回収する。 -/
theorem stableTriangleZeroHomLift_recovery :
    stableTriangleZeroHomLift s hZ ≫
        zeroFunctorLocusToStableHom (s.obj ⟨ULift.up 0⟩) (s.obj ⟨ULift.up 2⟩) =
      coherentTriangleLongHom s :=
  zeroStableHomFamilyLift_recovery _ _

end SerrePositivity.KST.Fibration
