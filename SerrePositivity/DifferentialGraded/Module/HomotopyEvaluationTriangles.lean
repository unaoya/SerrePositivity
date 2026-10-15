module
public import SerrePositivity.DifferentialGraded.Module.Pretriangulated
public import Mathlib.Algebra.Homology.HomotopyCategory.Triangulated

/-! # K(D)の評価関手によるdistinguished三角形の保存 -/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Pretriangulated

/-- shiftと可換な関手の可換squareから三角形の比較を得る。 -/
def mapTriangleSquareIso {C E K H : Type*} [Category* C] [Category* E] [Category* K] [Category* H]
    [HasShift C ℤ] [HasShift E ℤ] [HasShift K ℤ] [HasShift H ℤ]
    (Q : C ⥤ K) (G : K ⥤ H) (F : C ⥤ E) (q : E ⥤ H)
    [Q.CommShift ℤ] [G.CommShift ℤ] [F.CommShift ℤ] [q.CommShift ℤ]
    (α : Q ⋙ G ≅ F ⋙ q) [NatTrans.CommShift α.hom ℤ]
    (T : Triangle C) (T' : Triangle E) (e : F.mapTriangle.obj T ≅ T') :
    G.mapTriangle.obj (Q.mapTriangle.obj T) ≅ q.mapTriangle.obj T' :=
  (Functor.mapTriangleCompIso Q G).symm.app T ≪≫
    (Functor.mapTriangleIso α).app T ≪≫
    (Functor.mapTriangleCompIso F q).app T ≪≫ q.mapTriangle.mapIso e

variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 商に降ろした評価の因子分解同型。 -/
def moduleHomotopyEvaluationFacIso (x : D) :
    moduleToHomotopy A D ⋙ moduleHomotopyEvaluation A D x ≅
      moduleEvaluation A D x ⋙ _root_.HomotopyCategory.quotient (ModuleCat A) (.up ℤ) := by
  unfold moduleHomotopyEvaluation
  exact Quotient.lift.isLift _ _ _

instance moduleHomotopyEvaluationFacIsoCommShift (x : D) :
    NatTrans.CommShift (moduleHomotopyEvaluationFacIso A D x).hom ℤ := by
  unfold moduleHomotopyEvaluationFacIso moduleHomotopyEvaluation
  apply Quotient.liftCommShift_compatibility

/-- 評価されたK(D)の標準cone三角形と既存複体の標準cone三角形の比較。 -/
def moduleHomotopyConeTriangleEvaluationIso {M N : ModuleCategory A D} (f : M ⟶ N) (x : D) :=
  mapTriangleSquareIso (moduleToHomotopy A D) (moduleHomotopyEvaluation A D x)
    (moduleEvaluation A D x) (_root_.HomotopyCategory.quotient (ModuleCat A) (.up ℤ))
    (moduleHomotopyEvaluationFacIso A D x) (moduleConeTriangle A D f)
    (CochainComplex.mappingCone.triangle ((moduleEvaluation A D x).map f))
    (moduleConeTriangleEvaluationIso A D f x)

instance moduleHomotopyEvaluationIsTriangulated (x : D) :
    (moduleHomotopyEvaluation A D x).IsTriangulated where
  map_distinguished T hT := by
    change T ∈ moduleDistinguishedTriangles A D at hT
    obtain ⟨M, N, f, ⟨e⟩⟩ := hT
    exact isomorphic_distinguished _
      (_root_.HomotopyCategory.mappingCone_triangleh_distinguished
        ((moduleEvaluation A D x).map f)) _
      ((moduleHomotopyEvaluation A D x).mapTriangle.mapIso e ≪≫
        moduleHomotopyConeTriangleEvaluationIso A D f x)

end SerrePositivity.DifferentialGraded
