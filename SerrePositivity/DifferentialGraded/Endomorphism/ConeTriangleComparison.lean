module
public import SerrePositivity.DifferentialGraded.Endomorphism.ConeConnectingComparison
public import SerrePositivity.DifferentialGraded.Module.HomotopyEvaluationTriangles

/-! # 加群値dg関手の標準cone三角形比較と主Kでの三角性 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Pretriangulated
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable (B : Type w) [DGCategory A B] [Small.{u} B]
variable (F : DGFunctor A (RightModule A D) (RightModule A B))
local instance : F.onClosed.CommShift ℤ := dgModuleFunctorCommShift A D B F

/-- 正規化shift比較を用いた標準cone三角形の同型。 -/
def dgModuleFunctorConeTriangleIso {M N : ModuleCategory A D} (f : M ⟶ N) :
    moduleConeTriangle A B (F.onClosed.map f) ≅
      F.onClosed.mapTriangle.obj (moduleConeTriangle A D f) :=
  Triangle.isoMk (moduleConeTriangle A B (F.onClosed.map f))
    (F.onClosed.mapTriangle.obj (moduleConeTriangle A D f))
    (Iso.refl (F.onClosed.obj M)) (Iso.refl (F.onClosed.obj N))
    (dgModuleFunctorConeIso A D B F f)
    (by
      change F.onClosed.map f ≫ 𝟙 (F.onClosed.obj N) =
        𝟙 (F.onClosed.obj M) ≫ F.onClosed.map f
      rw [Category.comp_id, Category.id_comp])
    (by
      change moduleConeInr A B (F.onClosed.map f) ≫ dgModuleFunctorConeComparison A D B F f =
        𝟙 (F.onClosed.obj N) ≫ F.onClosed.map (moduleConeInr A D f)
      rw [Category.id_comp]
      exact dgModuleFunctorConeComparison_inr A D B F f)
    (by
      change moduleConeConnecting A B (F.onClosed.map f) ≫
        (CategoryTheory.shiftFunctor (ModuleCategory A B) (1 : ℤ)).map
          (𝟙 (F.onClosed.obj M)) =
        dgModuleFunctorConeComparison A D B F f ≫ F.onClosed.map (moduleConeConnecting A D f) ≫
          (normalizedDGModuleFunctorCommShiftIso A D B F 1).hom.app M
      rw [CategoryTheory.Functor.map_id, Category.comp_id]
      have he : (normalizedDGModuleFunctorCommShiftIso A D B F 1).hom.app M =
          (normalizedDGModuleFunctorShiftIso A D B F 1
            (ForgetEnrichment.to (Complex A) M)).hom := by
        simp only [normalizedDGModuleFunctorCommShiftIso, moduleShiftFunctor_eq]
        rfl
      rw [he]
      exact (dgModuleFunctorConeComparison_connecting A D B F f).symm)

local instance : F.onHomotopy.CommShift ℤ := dgModuleFunctorHomotopyCommShift A D B F

/-- 主Kの標準cone三角形の比較。因子分解自然同型のshift整合性を用いる。 -/
def dgModuleFunctorHomotopyConeTriangleIso {M N : ModuleCategory A D} (f : M ⟶ N) :
    F.onHomotopy.mapTriangle.obj (moduleHomotopyConeTriangle A D f) ≅
      moduleHomotopyConeTriangle A B (F.onClosed.map f) := by
  letI := dgModuleFunctorHomotopyFacIso_commShift A D B F
  exact mapTriangleSquareIso (moduleToHomotopy A D) F.onHomotopy F.onClosed
    (moduleToHomotopy A B) (dgModuleFunctorHomotopyFacIso A D B F)
    (moduleConeTriangle A D f) (moduleConeTriangle A B (F.onClosed.map f))
    (dgModuleFunctorConeTriangleIso A D B F f).symm

/-- 加群値dg関手の主K関手は正規化したshift構造について三角関手である。 -/
lemma dgModuleFunctorHomotopyIsTriangulated : F.onHomotopy.IsTriangulated where
  map_distinguished T hT := by
    change T ∈ moduleDistinguishedTriangles A D at hT
    obtain ⟨M, N, f, ⟨e⟩⟩ := hT
    exact isomorphic_distinguished _ (moduleHomotopyConeTriangle_distinguished A B
      (F.onClosed.map f)) _
      (F.onHomotopy.mapTriangle.mapIso e ≪≫ dgModuleFunctorHomotopyConeTriangleIso A D B F f)

end SerrePositivity.DifferentialGraded
