module
public import SerrePositivity.DifferentialGraded.Endomorphism.EnhancementComparison
public import SerrePositivity.DifferentialGraded.Functor.ModuleShift
public import SerrePositivity.DifferentialGraded.Functor.ModuleConeIso
public import SerrePositivity.DifferentialGraded.Tensor.Shift

/-! # 再構成Hom・tensorの評価成分のshift・cone図式

全次数dg写像でshiftの斉次単位とconeの包含を送る標準比較を使用する。
ここでは評価後の複体図式を与え、Perf上の三角同値は別の証明義務として残す。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable (E : RightModule A D)

/-- Hom(E,−)の正則End対象での評価。 -/
def endomorphismHomComponent : DGFunctor A (RightModule A D) (Complex A) :=
  (endomorphismModuleHom A D E).comp (moduleEvaluationDG A (EndomorphismObject E) .point)

lemma endomorphismHomComponent_obj (M : RightModule A D) :
    (endomorphismHomComponent A D E).obj M = moduleHom A D E M := rfl

lemma endomorphismHomComponent_eq :
    endomorphismHomComponent A D E = leftRepresentable A E := by
  apply EnrichedFunctor.ext (Complex A)
    (F := endomorphismHomComponent A D E) (G := leftRepresentable A E) (fun _ => rfl)
  intro M N
  simp only [eqToHom_refl, Category.comp_id]
  exact endomorphismModuleHom_map_π A D E M N

/-- 指定対象EとのtensorをDの対象dで評価する。 -/
def endomorphismTensorComponent (d : D) :
    DGFunctor A (RightModule A (EndomorphismObject E)) (Complex A) :=
  (endomorphismModuleTensor A D E).comp (moduleEvaluationDG A D d)

lemma endomorphismTensorComponent_obj (d : D) (N : RightModule A (EndomorphismObject E)) :
    (endomorphismTensorComponent A D E d).obj N =
      BalancedTensor.obj A (EndomorphismObject E) N ((endomorphismModuleAction A D E).leftAt d) :=
  rfl

lemma endomorphismTensorComponent_eq (d : D) :
    endomorphismTensorComponent A D E d =
      BalancedTensor.rightTensorDG A (EndomorphismObject E)
        ((endomorphismModuleAction A D E).leftAt d) := by
  apply EnrichedFunctor.ext (Complex A)
    (F := endomorphismTensorComponent A D E d)
    (G := BalancedTensor.rightTensorDG A (EndomorphismObject E)
      ((endomorphismModuleAction A D E).leftAt d)) (fun _ => rfl)
  intro M N
  simp only [eqToHom_refl, Category.comp_id]
  exact endomorphismModuleTensor_map_π A D E M N d

/-- 全Homのshift比較。Eの射影性やflat性は不要。 -/
def endomorphismHomShiftIso (s : ℤ) (M : RightModule A D) :
    moduleHom A D E (shiftModule s M) ≅ (moduleHom A D E M)⟦s⟧ :=
  DGFunctor.moduleShiftImageIso A D (endomorphismHomComponent A D E) s M

/-- 再構成tensorの各D成分でのshift比較。 -/
def endomorphismTensorShiftIso (d : D) (s : ℤ)
    (N : RightModule A (EndomorphismObject E)) :
    (endomorphismTensorComponent A D E d).obj (shiftModule s N) ≅
      ((endomorphismTensorComponent A D E d).obj N)⟦s⟧ :=
  DGFunctor.moduleShiftImageIso A (EndomorphismObject E)
    (endomorphismTensorComponent A D E d) s N

lemma endomorphismTensorShiftIso_eq (d : D) (s : ℤ)
    (N : RightModule A (EndomorphismObject E)) :
    endomorphismTensorShiftIso A D E d s N =
      BalancedTensor.rightTensorShiftIso A (EndomorphismObject E)
        ((endomorphismModuleAction A D E).leftAt d) s N := by
  apply Iso.ext
  apply HomologicalComplex.hom_ext
  intro i
  change (DGFunctor.moduleShiftImageComparison A (EndomorphismObject E)
      (endomorphismTensorComponent A D E d) s N).f i =
    (DGFunctor.moduleShiftImageComparison A (EndomorphismObject E)
      (BalancedTensor.rightTensorDG A (EndomorphismObject E)
        ((endomorphismModuleAction A D E).leftAt d)) s N).f i
  rw [DGFunctor.moduleShiftImageComparison_f, DGFunctor.moduleShiftImageComparison_f]
  exact congrArg (fun k => (k.f s (moduleShiftOutElement A (EndomorphismObject E) s N)).v
    i (i + s) rfl) (endomorphismModuleTensor_map_π A D E (shiftModule s N) N d)

/-- Hom(E,−)の標準coneに対する実際の複体同型。 -/
def endomorphismHomConeIso {M N : ModuleCategory A D} (f : M ⟶ N) :
    mappingCone (((endomorphismHomComponent A D E).toComplexFunctor A).map f) ≅
      ((endomorphismHomComponent A D E).toComplexFunctor A).obj (moduleCone A D f) :=
  DGFunctor.moduleConeImageIso A D (endomorphismHomComponent A D E) f

/-- tensorの標準coneに対する各D成分の複体同型。 -/
def endomorphismTensorConeIso (d : D)
    {M N : ModuleCategory A (EndomorphismObject E)} (f : M ⟶ N) :
    mappingCone (((endomorphismTensorComponent A D E d).toComplexFunctor A).map f) ≅
      ((endomorphismTensorComponent A D E d).toComplexFunctor A).obj
        (moduleCone A (EndomorphismObject E) f) :=
  DGFunctor.moduleConeImageIso A (EndomorphismObject E) (endomorphismTensorComponent A D E d) f

lemma endomorphismHomConeIso_inr {M N : ModuleCategory A D} (f : M ⟶ N) :
    mappingCone.inr (((endomorphismHomComponent A D E).toComplexFunctor A).map f) ≫
        (endomorphismHomConeIso A D E f).hom =
      ((endomorphismHomComponent A D E).toComplexFunctor A).map (moduleConeInr A D f) :=
  DGFunctor.moduleConeImageComparison_inr A D (endomorphismHomComponent A D E) f

lemma endomorphismHomConeIso_inl {M N : ModuleCategory A D} (f : M ⟶ N) :
    (mappingCone.inl (((endomorphismHomComponent A D E).toComplexFunctor A).map f)).comp
        (Cochain.ofHom (endomorphismHomConeIso A D E f).hom) (add_zero (-1)) =
      DGFunctor.moduleConeImageInl A D (endomorphismHomComponent A D E) f :=
  DGFunctor.moduleConeImageComparison_inl A D (endomorphismHomComponent A D E) f

lemma endomorphismTensorConeIso_inr (d : D)
    {M N : ModuleCategory A (EndomorphismObject E)} (f : M ⟶ N) :
    mappingCone.inr (((endomorphismTensorComponent A D E d).toComplexFunctor A).map f) ≫
        (endomorphismTensorConeIso A D E d f).hom =
      ((endomorphismTensorComponent A D E d).toComplexFunctor A).map
        (moduleConeInr A (EndomorphismObject E) f) :=
  DGFunctor.moduleConeImageComparison_inr A (EndomorphismObject E)
    (endomorphismTensorComponent A D E d) f

lemma endomorphismTensorConeIso_inl (d : D)
    {M N : ModuleCategory A (EndomorphismObject E)} (f : M ⟶ N) :
    (mappingCone.inl (((endomorphismTensorComponent A D E d).toComplexFunctor A).map f)).comp
        (Cochain.ofHom (endomorphismTensorConeIso A D E d f).hom) (add_zero (-1)) =
      DGFunctor.moduleConeImageInl A (EndomorphismObject E)
        (endomorphismTensorComponent A D E d) f :=
  DGFunctor.moduleConeImageComparison_inl A (EndomorphismObject E)
    (endomorphismTensorComponent A D E d) f

end SerrePositivity.DifferentialGraded
