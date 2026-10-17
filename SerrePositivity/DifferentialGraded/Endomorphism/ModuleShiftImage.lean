module
public import SerrePositivity.DifferentialGraded.Endomorphism.ModuleConeImage
public import SerrePositivity.DifferentialGraded.Functor.ModuleShift

/-! # 加群値dg関手のshift比較同型を全次数自然な加群同型に組み立てる -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Opposite HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (B : Type w) [DGCategory A B] [Small.{u} B]

lemma moduleShiftRepresentation_naturality (s : ℤ) {U V : RightModule A B}
    (a : (moduleHom A B U V).X s)
    (c : ∀ x : Bᵒᵖ, U.obj x ⟶ (shiftModule s V).obj x)
    (hc : ∀ (x : Bᵒᵖ) (i : ℤ), (c x).f i =
      ((moduleHomπ A B U V x.unop).f s a).v i (i + s) rfl) :
    ∀ x y, U.map x y ≫ homPostcompose (U.obj x) (c y) =
      (shiftModule s V).map x y ≫ homPrecompose (c x) ((shiftModule s V).obj y) := by
  apply closedFamily_of_action A c
  intro x y p r n hn f v
  change (c y).f n (((U.map x y).f p f).v r n hn v) =
    (((shiftModule s V).map x y).f p f).v r n hn ((c x).f r v)
  rw [hc, hc, shiftModule_map_v]
  have h := congrArg (fun z => z.v r (n + s) (by omega))
    (moduleHomElement_naturality A B s a x y p f)
  rw [Cochain.comp_v _ _ _ r n (n + s) hn rfl, Cochain.units_smul_v,
    Cochain.comp_v _ _ _ r (r + s) (n + s) rfl (by omega)] at h
  exact congrArg (fun k => k v) h

variable (D : Type v) [DGCategory A D] [Small.{u} D]
variable (F : DGFunctor A (RightModule A D) (RightModule A B))

lemma dgModuleFunctorShift_naturality (s : ℤ) (M : RightModule A D) :
    ∀ x y, (F.obj (shiftModule s M)).map x y ≫
        homPostcompose ((F.obj (shiftModule s M)).obj x)
          (DGFunctor.moduleShiftImageIso A D (F.comp (moduleEvaluationDG A B y.unop)) s M).hom =
      (shiftModule s (F.obj M)).map x y ≫
        homPrecompose
          (DGFunctor.moduleShiftImageIso A D (F.comp (moduleEvaluationDG A B x.unop)) s M).hom
          ((shiftModule s (F.obj M)).obj y) := by
  apply moduleShiftRepresentation_naturality A B s
    ((F.map (shiftModule s M) M).f s (moduleShiftOutElement A D s M))
  intro x i
  exact DGFunctor.moduleShiftImageComparison_f A D (F.comp (moduleEvaluationDG A B x.unop)) s M i

/-- 評価成分のshift同型を、主加群の全次数自然な同型へ組み立てる。 -/
def dgModuleFunctorShiftIso (s : ℤ) (M : RightModule A D) :
    ForgetEnrichment.of (Complex A) (F.obj (shiftModule s M)) ≅
      ForgetEnrichment.of (Complex A) (shiftModule s (F.obj M)) :=
  moduleIsoMk A B
    (fun x => DGFunctor.moduleShiftImageIso A D (F.comp (moduleEvaluationDG A B x.unop)) s M)
    (dgModuleFunctorShift_naturality A B D F s M)

lemma dgModuleFunctorShiftIso_hom_eval (s : ℤ) (M : RightModule A D) (b : B) :
    (moduleEvaluation A B b).map (dgModuleFunctorShiftIso A B D F s M).hom =
      (DGFunctor.moduleShiftImageIso A D (F.comp (moduleEvaluationDG A B b)) s M).hom :=
  moduleIsoMk_hom_eval A B _ _ b

end SerrePositivity.DifferentialGraded
