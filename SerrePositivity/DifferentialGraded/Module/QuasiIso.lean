module
public import SerrePositivity.DifferentialGraded.Module.Category
public import SerrePositivity.DifferentialGraded.Module.Homotopy
public import Mathlib.Algebra.Homology.QuasiIso

/-! # 右 dg 加群の objectwise 準同型

局所化する射のクラスを Mathlib の MorphismProperty として固定する。
任意可換環上の非有界複体を評価し、モデル構造の存在を仮定しない。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory HomologicalComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 各対象での評価が既存複体の quasiIso となる閉次数零射。 -/
def moduleQuasiIso : MorphismProperty (ModuleCategory A D) :=
  fun _ _ f => ∀ x : D, QuasiIso ((moduleEvaluation A D x).map f)

@[simp]
lemma moduleQuasiIso_iff {M N : ModuleCategory A D} (f : M ⟶ N) :
    moduleQuasiIso A D f ↔ ∀ x : D, QuasiIso ((moduleEvaluation A D x).map f) := Iff.rfl

/-- 指定評価への quasiIso の逆像すべての共通部分。 -/
lemma moduleQuasiIso_eq_iInf : moduleQuasiIso A D =
    ⨅ x : D, (HomologicalComplex.quasiIso (ModuleCat A) (.up ℤ)).inverseImage
      (moduleEvaluation A D x) := by
  ext M N f
  simp [moduleQuasiIso, MorphismProperty.iInf_iff, MorphismProperty.inverseImage]

instance moduleQuasiIsoIsMultiplicative : (moduleQuasiIso A D).IsMultiplicative where
  id_mem M x := by
    rw [CategoryTheory.Functor.map_id]
    infer_instance
  comp_mem f g hf hg x := by
    have := hf x
    have := hg x
    rw [CategoryTheory.Functor.map_comp]
    infer_instance

instance moduleQuasiIsoHasTwoOutOfThree : (moduleQuasiIso A D).HasTwoOutOfThreeProperty where
  of_postcomp f g hg hfg x := by
    have := hg x
    have : QuasiIso ((moduleEvaluation A D x).map f ≫
        (moduleEvaluation A D x).map g) := by
      simpa only [← CategoryTheory.Functor.map_comp] using hfg x
    exact quasiIso_of_comp_right ((moduleEvaluation A D x).map f)
      ((moduleEvaluation A D x).map g)
  of_precomp f g hf hfg x := by
    have := hf x
    have : QuasiIso ((moduleEvaluation A D x).map f ≫
        (moduleEvaluation A D x).map g) := by
      simpa only [← CategoryTheory.Functor.map_comp] using hfg x
    exact quasiIso_of_comp_left ((moduleEvaluation A D x).map f)
      ((moduleEvaluation A D x).map g)

instance moduleQuasiIsoStableUnderRetracts : (moduleQuasiIso A D).IsStableUnderRetracts where
  of_retract h hg x := by
    have := hg x
    exact quasiIso_of_retractArrow (h.map (moduleEvaluation A D x))

instance moduleQuasiIsoRespectsIso : (moduleQuasiIso A D).RespectsIso := by
  rw [moduleQuasiIso_eq_iInf]
  infer_instance

/-- objectwise な判定はすべての評価関手が指定射を送ることと同じ。 -/
lemma moduleQuasiIso_evaluation (x : D) : moduleQuasiIso A D ≤
    (HomologicalComplex.quasiIso (ModuleCat A) (.up ℤ)).inverseImage
      (moduleEvaluation A D x) := fun _ _ _ hf => hf x

/-- 全 dg 自然な加群ホモトピーはすべての評価ホモロジー写像を同一視する。 -/
lemma moduleHomotopy_homologyMap_eq {M N : ModuleCategory A D} {f g : M ⟶ N}
    (h : ModuleHomotopy A D f g) (x : D) (i : ℤ) :
    homologyMap ((moduleEvaluation A D x).map f) i =
      homologyMap ((moduleEvaluation A D x).map g) i :=
  (moduleHomotopy_evaluation A D h x).some.homologyMap_eq i

/-- 指定する quasiIso のクラスは加群ホモトピーで不変。 -/
lemma moduleQuasiIso_iff_of_homotopy {M N : ModuleCategory A D} {f g : M ⟶ N}
    (h : ModuleHomotopy A D f g) : moduleQuasiIso A D f ↔ moduleQuasiIso A D g := by
  simp only [moduleQuasiIso_iff, quasiIso_iff, quasiIsoAt_iff_isIso_homologyMap]
  apply forall_congr'
  intro x
  apply forall_congr'
  intro i
  rw [moduleHomotopy_homologyMap_eq A D h x i]

/-- K(D) で同じ射を表す閉零射は同じ quasiIso 判定を持つ。 -/
lemma moduleQuasiIso_iff_of_homotopy_map_eq {M N : ModuleCategory A D} {f g : M ⟶ N}
    (h : (moduleToHomotopy A D).map f = (moduleToHomotopy A D).map g) :
    moduleQuasiIso A D f ↔ moduleQuasiIso A D g := by
  obtain ⟨hh⟩ := (moduleToHomotopy_map_eq_iff A D f g).1 h
  exact moduleQuasiIso_iff_of_homotopy A D hh

end SerrePositivity.DifferentialGraded
