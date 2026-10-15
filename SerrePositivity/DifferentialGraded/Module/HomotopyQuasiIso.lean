module
public import SerrePositivity.DifferentialGraded.Module.QuasiIso
public import Mathlib.Algebra.Homology.Localization

/-! # K(D) 上の objectwise quasiIso と閉零圏からの比較 -/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- K(D) の射をすべての既存複体ホモトピー圏の評価で判定する。 -/
def moduleHomotopyQuasiIso : MorphismProperty (ModuleHomotopyCategory A D) :=
  fun _ _ f => ∀ x : D, _root_.HomotopyCategory.quasiIso (ModuleCat A) (.up ℤ)
    ((moduleHomotopyEvaluation A D x).map f)

/-- K(D) の対象ごとのホモロジー。 -/
def moduleHomotopyHomology (x : D) (i : ℤ) : ModuleHomotopyCategory A D ⥤ ModuleCat A :=
  moduleHomotopyEvaluation A D x ⋙ _root_.HomotopyCategory.homologyFunctor
    (ModuleCat A) (.up ℤ) i

lemma moduleHomotopyQuasiIso_iff {M N : ModuleHomotopyCategory A D} (f : M ⟶ N) :
    moduleHomotopyQuasiIso A D f ↔
      ∀ (x : D) (i : ℤ), IsIso ((moduleHomotopyHomology A D x i).map f) := Iff.rfl

lemma moduleHomotopyQuasiIso_eq_iInf : moduleHomotopyQuasiIso A D =
    ⨅ (x : D) (i : ℤ), (MorphismProperty.isomorphisms (ModuleCat A)).inverseImage
      (moduleHomotopyHomology A D x i) := by
  ext M N f
  simp only [moduleHomotopyQuasiIso_iff, MorphismProperty.iInf_iff,
    MorphismProperty.inverseImage_iff, MorphismProperty.isomorphisms.iff]

instance moduleHomotopyQuasiIsoRespectsIso :
    (moduleHomotopyQuasiIso A D).RespectsIso := by
  rw [moduleHomotopyQuasiIso_eq_iInf]
  infer_instance

instance moduleHomotopyQuasiIsoIsMultiplicative :
    (moduleHomotopyQuasiIso A D).IsMultiplicative where
  id_mem M x i := by
    change IsIso ((moduleHomotopyHomology A D x i).map (𝟙 M))
    rw [CategoryTheory.Functor.map_id]
    infer_instance
  comp_mem f g hf hg x i := by
    have : IsIso ((moduleHomotopyHomology A D x i).map f) := hf x i
    have : IsIso ((moduleHomotopyHomology A D x i).map g) := hg x i
    change IsIso ((moduleHomotopyHomology A D x i).map (f ≫ g))
    rw [CategoryTheory.Functor.map_comp]
    infer_instance

instance moduleHomotopyQuasiIsoHasTwoOutOfThree :
    (moduleHomotopyQuasiIso A D).HasTwoOutOfThreeProperty where
  of_postcomp f g hg hfg x i := by
    let W := (MorphismProperty.isomorphisms (ModuleCat A)).inverseImage
      (moduleHomotopyHomology A D x i)
    exact W.of_postcomp (W' := W) f g (hg x i) (hfg x i)
  of_precomp f g hf hfg x i := by
    let W := (MorphismProperty.isomorphisms (ModuleCat A)).inverseImage
      (moduleHomotopyHomology A D x i)
    exact W.of_precomp (W' := W) f g (hf x i) (hfg x i)

instance moduleHomotopyQuasiIsoStableUnderRetracts :
    (moduleHomotopyQuasiIso A D).IsStableUnderRetracts where
  of_retract h hg x i :=
    MorphismProperty.of_retract
      (P := (MorphismProperty.isomorphisms (ModuleCat A)).inverseImage
        (moduleHomotopyHomology A D x i)) h (hg x i)

/-- K(D) の quasiIso の逆像は、指定した閉零加群の quasiIso と一致する。 -/
lemma moduleHomotopyQuasiIso_map_iff {M N : ModuleCategory A D} (f : M ⟶ N) :
    moduleHomotopyQuasiIso A D ((moduleToHomotopy A D).map f) ↔
      moduleQuasiIso A D f := by
  change (∀ x : D, _root_.HomotopyCategory.quasiIso (ModuleCat A) (.up ℤ)
    ((moduleHomotopyEvaluation A D x).map ((moduleToHomotopy A D).map f))) ↔ _
  change (∀ x : D, _root_.HomotopyCategory.quasiIso (ModuleCat A) (.up ℤ)
    ((_root_.HomotopyCategory.quotient (ModuleCat A) (.up ℤ)).map
      ((moduleEvaluation A D x).map f))) ↔ _
  simp only [_root_.HomotopyCategory.quotient_map_mem_quasiIso_iff,
    HomologicalComplex.mem_quasiIso_iff, moduleQuasiIso_iff]

lemma moduleHomotopyQuasiIso_inverseImage :
    (moduleHomotopyQuasiIso A D).inverseImage (moduleToHomotopy A D) =
      moduleQuasiIso A D := by
  ext M N f
  exact moduleHomotopyQuasiIso_map_iff A D f

end SerrePositivity.DifferentialGraded
