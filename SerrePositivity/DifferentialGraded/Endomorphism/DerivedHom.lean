module
public import SerrePositivity.DifferentialGraded.Endomorphism.ModuleAdjunction
public import SerrePositivity.DifferentialGraded.Derived.ProjectiveHomQuasiIso

/-! # 指定射影的dg加群からのHomの導来化

Eのホモトピー射影性を明示し、Hom(E,−)が擬同型を保つことから指定局所化へ降ろす。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Opposite HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable (E : RightModule A D)

/-- Hom関手の閉零成分は主Hom endの後合成射に等しい。 -/
lemma endomorphismModuleHom_map_eval (M M' : RightModule A D)
    (f : ForgetEnrichment.of (Complex A) M ⟶ ForgetEnrichment.of (Complex A) M')
    (b : EndomorphismObject E) :
    (moduleEvaluation A (EndomorphismObject E) b).map
      ((endomorphismModuleHom A D E).onClosed.map f) =
    eHomWhiskerLeft (Complex A) (ForgetEnrichment.of (Complex A) E) f := by
  cases b
  apply HomologicalComplex.hom_ext
  intro r
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro m
  apply moduleHomElement_ext A D
  intro d
  apply Cochain.ext
  intro s n hn
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro t
  have h := congrArg (fun k => (k.f r m).v s n hn t)
    (moduleHomWhiskerLeft_π A D (M := ForgetEnrichment.of (Complex A) E) f d)
  change ((moduleHomπ A D E M' d).f r
      ((eHomWhiskerLeft (Complex A) (ForgetEnrichment.of (Complex A) E) f).f r m)).v s n hn t =
    ((homPostcompose (E.obj (op d)) ((moduleEvaluation A D d).map f)).f r
      ((moduleHomπ A D E M d).f r m)).v s n hn t at h
  rw [homPostcompose_apply, Cochain.comp_zero_cochain_v, Cochain.ofHom_v] at h
  exact (endomorphismModuleHom_map_eval_apply A D E M M' f d m t hn).trans h.symm

/-- Eのホモトピー射影性の下でHom(E,−)は指定擬同型を保つ。 -/
lemma endomorphismModuleHom_quasiIso
    (hE : moduleHomotopicallyProjective A D (ForgetEnrichment.of (Complex A) E))
    {M M' : ModuleCategory A D} (f : M ⟶ M') (hf : moduleQuasiIso A D f) :
    moduleQuasiIso A (EndomorphismObject E) ((endomorphismModuleHom A D E).onClosed.map f) := by
  intro b
  rw [endomorphismModuleHom_map_eval]
  exact moduleHomotopicallyProjective_postcompose_quasiIso A D hE f hf

/-- 局所化後のHom関手は、元の指定擬同型を反転する。 -/
lemma endomorphismModuleHomToDerived_inverts
    (hE : moduleHomotopicallyProjective A D (ForgetEnrichment.of (Complex A) E)) :
    (moduleQuasiIso A D).IsInvertedBy
      ((endomorphismModuleHom A D E).onClosed ⋙ moduleToDerived A (EndomorphismObject E)) :=
  fun _ _ f hf => moduleToDerived_inverts A (EndomorphismObject E) _
    (endomorphismModuleHom_quasiIso A D E hE f hf)

/-- 射影的指定対象のHomを主導来加群圏間の関手へ降ろす。 -/
def endomorphismDerivedHom
    (hE : moduleHomotopicallyProjective A D (ForgetEnrichment.of (Complex A) E)) :
    DerivedModuleCategory A D ⥤ DerivedModuleCategory A (EndomorphismObject E) :=
  moduleDerivedLift A D
    ((endomorphismModuleHom A D E).onClosed ⋙ moduleToDerived A (EndomorphismObject E))
    (endomorphismModuleHomToDerived_inverts A D E hE)

/-- 導来Homの構成は指定局所化との厳密な可換式を持つ。 -/
lemma endomorphismDerivedHom_fac
    (hE : moduleHomotopicallyProjective A D (ForgetEnrichment.of (Complex A) E)) :
    moduleToDerived A D ⋙ endomorphismDerivedHom A D E hE =
      (endomorphismModuleHom A D E).onClosed ⋙ moduleToDerived A (EndomorphismObject E) :=
  moduleDerivedLift_fac A D _ _

/-- U13のperfect dg代表に保持された射影性を使う導来Hom。 -/
def perfectEndomorphismDerivedHom (S : Set D) (E : PerfectDGModuleOver A D S) :
    DerivedModuleCategory A D ⥤ DerivedModuleCategory A (EndomorphismObject E.val) :=
  endomorphismDerivedHom A D E.val E.property.1

end SerrePositivity.DifferentialGraded
