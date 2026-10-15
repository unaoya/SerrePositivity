module
public import SerrePositivity.DifferentialGraded.Module.ConeShiftSquares

/-! # 標準cone三角形の整数shift比較 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Pretriangulated
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 明示的な加群shift射を可換条件として受け取る三角形shiftの同型構成子。 -/
def moduleTriangleShiftIsoMk (s : ℤ) (T T' : Triangle (ModuleCategory A D))
    (e₁ : moduleShiftObj A D s T.obj₁ ≅ T'.obj₁)
    (e₂ : moduleShiftObj A D s T.obj₂ ≅ T'.obj₂)
    (e₃ : moduleShiftObj A D s T.obj₃ ≅ T'.obj₃)
    (h₁ : (s.negOnePow • moduleShiftMap A D s T.mor₁) ≫ e₂.hom = e₁.hom ≫ T'.mor₁)
    (h₂ : (s.negOnePow • moduleShiftMap A D s T.mor₂) ≫ e₃.hom = e₂.hom ≫ T'.mor₂)
    (h₃ : (s.negOnePow • (moduleShiftMap A D s T.mor₃ ≫
      (shiftFunctorComm (ModuleCategory A D) 1 s).hom.app T.obj₁)) ≫ e₁.hom⟦(1 : ℤ)⟧' =
        e₃.hom ≫ T'.mor₃) :
    (Triangle.shiftFunctor (ModuleCategory A D) s).obj T ≅ T' :=
  by
    refine Triangle.isoMk _ _ e₁ e₂ e₃ ?_ ?_ ?_
    · dsimp only [Triangle.shiftFunctor, Triangle.mk, moduleShiftFunctor_eq,
        moduleShiftFunctor] at h₁ ⊢
      exact h₁
    · dsimp only [Triangle.shiftFunctor, Triangle.mk, moduleShiftFunctor_eq,
        moduleShiftFunctor] at h₂ ⊢
      exact h₂
    · dsimp only [Triangle.shiftFunctor, Triangle.mk, moduleShiftFunctor_eq,
        moduleShiftFunctor] at h₃ ⊢
      exact h₃

lemma moduleConeShift_connecting_id (s : ℤ) {M N : ModuleCategory A D} (f : M ⟶ N) :
    (s.negOnePow • (moduleShiftMap A D s (moduleConeConnecting A D f) ≫
      (shiftFunctorComm (ModuleCategory A D) 1 s).hom.app M)) ≫
        (𝟙 (moduleShiftObj A D s M))⟦(1 : ℤ)⟧' =
          moduleConeShiftHom A D s f ≫ moduleConeConnecting A D (moduleShiftMap A D s f) := by
  have hi := (CategoryTheory.shiftFunctor (ModuleCategory A D) (1 : ℤ)).map_id
    (moduleShiftObj A D s M)
  exact (congrArg (fun a => (s.negOnePow •
    (moduleShiftMap A D s (moduleConeConnecting A D f) ≫
      (shiftFunctorComm (ModuleCategory A D) 1 s).hom.app M)) ≫ a) hi).trans
        ((Category.comp_id _).trans (moduleConeShift_connecting A D s f))

def moduleConeTriangleShiftIso (s : ℤ) {M N : ModuleCategory A D} (f : M ⟶ N) :
    (Triangle.shiftFunctor (ModuleCategory A D) s).obj (moduleConeTriangle A D f) ≅
      moduleConeTriangle A D (moduleShiftMap A D s f) :=
  moduleTriangleShiftIsoMk A D s (moduleConeTriangle A D f)
    (moduleConeTriangle A D (moduleShiftMap A D s f))
    (Iso.refl (moduleShiftObj A D s M))
    (moduleShiftSignIso A D s (moduleShiftObj A D s N)) (moduleConeShiftIso A D s f)
    (moduleShiftSignSquare A D s (moduleShiftMap A D s f))
    (moduleConeShift_inr A D s f) (moduleConeShift_connecting_id A D s f)


end SerrePositivity.DifferentialGraded
