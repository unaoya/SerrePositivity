module

public import SerrePositivity.AlgebraicGeometry.CechConstantComplex

/-!
概要：元の定数列から同じ零次singleへの射影を比較する。
方針：元の包含との合成と既存の擬同型の消去を使う。
規約：係数環と加群の宇宙を分け、元の各項と微分を保つ。
使われ方：F8の全複体から同じ定数列の正次数を除く比較。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory
universe u v
variable {R : Type v} [CommRing R] (A : ModuleCat.{u} R)

set_option backward.isDefEq.respectTransparency false in
/-- 元の定数列から同じ零次singleへの標準射影。 -/
def cechConstantSingleProjection :
    cechConstantComplex A ⟶
      (HomologicalComplex.single (ModuleCat.{u} R) (.up ℕ) 0).obj A :=
  HomologicalComplex.mkHomToSingle (𝟙 A) (by intro i hi; change i + 1 = 0 at hi; omega)

set_option backward.isDefEq.respectTransparency false in
/-- 同じ射影の零次成分は元のsingleの標準同型の逆。 -/
theorem cechConstantSingleProjection_f_zero :
    (cechConstantSingleProjection A).f 0 =
      (HomologicalComplex.singleObjXSelf (.up ℕ) 0 A).inv := by
  exact (HomologicalComplex.mkHomToSingle_f
    (K := cechConstantComplex A) (𝟙 A) _).trans (Category.id_comp _)

set_option backward.isDefEq.respectTransparency false in
/-- 元の包含と同じ射影の合成は零次singleの恒等。 -/
theorem cechConstantSingleAugmentation_projection :
    cechConstantSingleAugmentation A ≫ cechConstantSingleProjection A = 𝟙 _ := by
  apply HomologicalComplex.from_single_hom_ext
  change (cechConstantSingleAugmentation A).f 0 ≫
    (cechConstantSingleProjection A).f 0 = 𝟙 _
  exact (congrArg₂ (fun f g ↦ f ≫ g)
    (cechConstantSingleAugmentation_f_zero A)
    (cechConstantSingleProjection_f_zero A)).trans
      (HomologicalComplex.singleObjXSelf (.up ℕ) 0 A).hom_inv_id

/-- 同じ射影は、元の包含の擬同型性から得られる擬同型。 -/
theorem cechConstantSingleProjection_quasiIso : QuasiIso (cechConstantSingleProjection A) := by
  letI := cechConstantSingleAugmentation_quasiIso A
  haveI : QuasiIso (cechConstantSingleAugmentation A ≫ cechConstantSingleProjection A) := by
    rw [cechConstantSingleAugmentation_projection]
    infer_instance
  exact _root_.quasiIso_of_comp_left
    (cechConstantSingleAugmentation A) (cechConstantSingleProjection A)

/-- 同じ射影の各成分は全射。 -/
theorem cechConstantSingleProjection_surjective (n : ℕ) :
    Function.Surjective ((cechConstantSingleProjection A).f n).hom := by
  cases n with
  | zero =>
    rw [cechConstantSingleProjection_f_zero]
    intro x
    refine ⟨(HomologicalComplex.singleObjXSelf (.up ℕ) 0 A).hom.hom x, ?_⟩
    exact congrArg (fun f ↦ f.hom x)
      (HomologicalComplex.singleObjXSelf (.up ℕ) 0 A).hom_inv_id
  | succ n =>
    let h := HomologicalComplex.isZero_single_obj_X (.up ℕ) 0 A (n + 1) (by omega)
    haveI : Epi ((cechConstantSingleProjection A).f (n + 1)) :=
      h.epi _
    exact (ModuleCat.epi_iff_surjective _).mp inferInstance

end SerrePositivity.AlgebraicGeometry
