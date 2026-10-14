module
public import SerrePositivity.DifferentialGraded.Module.Cone
public import SerrePositivity.DifferentialGraded.Module.ShiftCoherence
public import SerrePositivity.DifferentialGraded.Complexes.ConeMaps

/-! # cone の connecting map と objectwise triangle -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Pretriangulated Opposite HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 既存 cone triangle の connecting map を全次数自然な加群射へ持ち上げる。 -/
def moduleConeConnecting {M N : ModuleCategory A D} (f : M ⟶ N) :
    moduleCone A D f ⟶ M⟦(1 : ℤ)⟧ :=
  moduleMorphismMk A D (M := ForgetEnrichment.to (Complex A) (moduleCone A D f))
    (N := shiftModule 1 (ForgetEnrichment.to (Complex A) M))
    (fun x => (mappingCone.triangle
      (closedTransApp A (moduleClosedHomEquiv A D M N f) x)).mor₃) (by
        intro x y
        exact coneHomMap_connecting _ _ _ _
          (closedTransApp_naturality A (moduleClosedHomEquiv A D M N f) x y))

/-- connecting map の評価は既存複体 cone triangle の第三射。 -/
@[simp] lemma moduleConeConnecting_eval {M N : ModuleCategory A D} (f : M ⟶ N) (x : D) :
    (moduleEvaluation A D x).map (moduleConeConnecting A D f) =
      (mappingCone.triangle ((moduleEvaluation A D x).map f)).mor₃ := by
  unfold moduleConeConnecting
  rw [moduleMorphismMk_eval]
  rfl

/-- 加群圏の標準 cone triangle。distinguished の主張はホモトピー/導来圏で行う。 -/
def moduleConeTriangle {M N : ModuleCategory A D} (f : M ⟶ N) : Triangle (ModuleCategory A D) :=
  Triangle.mk f (moduleConeInr A D f) (moduleConeConnecting A D f)

/-- 評価した標準 cone triangle と既存複体の標準 triangle の比較。 -/
def moduleConeTriangleEvaluationIso {M N : ModuleCategory A D} (f : M ⟶ N) (x : D) :
    (moduleEvaluation A D x).mapTriangle.obj (moduleConeTriangle A D f) ≅
      mappingCone.triangle ((moduleEvaluation A D x).map f) :=
  Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by simp only [moduleConeTriangle, Functor.mapTriangle_obj, Triangle.mk_mor₁,
      mappingCone.triangle_mor₁, Iso.refl_hom, Category.comp_id, Category.id_comp])
    (by simp only [moduleConeTriangle, Functor.mapTriangle_obj, Triangle.mk_mor₂,
      mappingCone.triangle_mor₂, Iso.refl_hom, Category.comp_id, Category.id_comp,
      moduleConeInr_eval])
    (by
      simp only [moduleConeTriangle, Functor.mapTriangle_obj, Triangle.mk_mor₃,
        Iso.refl_hom, CategoryTheory.Functor.map_id, Category.comp_id, Category.id_comp,
        moduleConeConnecting_eval]
      change (mappingCone.triangle ((moduleEvaluation A D x).map f)).mor₃ =
        (mappingCone.triangle ((moduleEvaluation A D x).map f)).mor₃ ≫ 𝟙 _
      rw [Category.comp_id])
end SerrePositivity.DifferentialGraded
