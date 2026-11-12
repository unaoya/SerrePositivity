module
public import SerrePositivity.DifferentialGraded.Functor.ModuleShift
public import SerrePositivity.DifferentialGraded.Module.Hom.ColimitsAndRightHom
/-!
概要：加群値 dg 関手と実 shift の比較同型。
方針：同じ標準比較を全評価で検証して同型を反映する。
規約：各評価の任意の同型を選ばない。
使われ方：代表加群の shift による表現可能性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
section
open CategoryTheory MonoidalCategory Opposite DifferentialGraded
open HomologicalComplex CochainComplex HomComplex
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
    (E : Type w) [DGCategory R E] [Small.{u} E]
    (F : DGFunctor R (RightModule R D) (RightModule R E)) (s : ℤ) (M : RightModule R D)

lemma dgModuleFunctorShiftComparison_naturality (x y : Eᵒᵖ) :
    (F.obj (shiftModule s M)).map x y ≫
      homPostcompose ((F.obj (shiftModule s M)).obj x)
        (DGFunctor.moduleShiftImageComparison R D (F.comp (moduleEvaluationDG R E y.unop)) s M) =
      (shiftModule s (F.obj M)).map x y ≫
        homPrecompose
          (DGFunctor.moduleShiftImageComparison R D (F.comp (moduleEvaluationDG R E x.unop)) s M)
          ((shiftModule s (F.obj M)).obj y) := by
  apply closedFamily_of_action R
    (M := F.obj (shiftModule s M)) (N := shiftModule s (F.obj M))
    (fun x ↦ DGFunctor.moduleShiftImageComparison R D
      (F.comp (moduleEvaluationDG R E x.unop)) s M)
  intro x y p r n hn f v
  rw [DGFunctor.moduleShiftImageComparison_f, DGFunctor.moduleShiftImageComparison_f]
  unfold moduleAction
  rw [shiftModule_map_v]
  have h := moduleHomElement_naturality R E s
    ((F.map (shiftModule s M) M).f s (moduleShiftOutElement R D s M)) x y p f
  have hv := congrArg (fun c ↦ c.v r (n + s) (by omega) v) h
  rw [Cochain.comp_v _ _ _ r n (n + s) hn rfl,
    Cochain.units_smul_v,
    Cochain.comp_v _ _ _ r (r + s) (n + s) rfl (by omega)] at hv
  exact hv

def dgModuleFunctorShiftComparison :
    ForgetEnrichment.of (Complex R) (F.obj (shiftModule s M)) ⟶
      ForgetEnrichment.of (Complex R) (shiftModule s (F.obj M)) :=
  moduleMorphismMk R E
    (fun x ↦ DGFunctor.moduleShiftImageComparison R D
      (F.comp (moduleEvaluationDG R E x.unop)) s M)
    (dgModuleFunctorShiftComparison_naturality R D E F s M)

lemma dgModuleFunctorShiftComparison_isIso :
    IsIso (dgModuleFunctorShiftComparison R D E F s M) := by
  apply moduleIsIso_of_evaluations R E
  intro x
  change IsIso ((moduleEvaluation R E x).map (moduleMorphismMk R E _ _))
  rw [moduleMorphismMk_eval]
  infer_instance

def dgModuleFunctorShiftIso :
    ForgetEnrichment.of (Complex R) (F.obj (shiftModule s M)) ≅
      ForgetEnrichment.of (Complex R) (shiftModule s (F.obj M)) := by
  let := dgModuleFunctorShiftComparison_isIso R D E F s M
  exact asIso (dgModuleFunctorShiftComparison R D E F s M)

end

end SerrePositivity.InfinityCategories.Project.DerivedCategories
