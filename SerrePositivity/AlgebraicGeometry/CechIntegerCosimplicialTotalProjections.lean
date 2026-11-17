module

public import SerrePositivity.AlgebraicGeometry.CechIntegerTotalToColumnZeroQuasiIso
public import SerrePositivity.AlgebraicGeometry.CechIntegerLiftTotalFunctor
public import SerrePositivity.AlgebraicGeometry.CechIntegerLiftTotalQuasiIso
public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
import all SerrePositivity.HomologicalAlgebra.BicomplexProjection

/-!
概要：被覆の余単体変数を残し、同じ共通totalから二つの元の軸へ射影する。
方針：既存の自然な射影の全射擬同型性を、同じ交代余面複体とtotalへ渡す。
規約：三方向のtotalの結合則や対角線消去を新しく作らない。
使われ方：相対fppfの二つの軸を、同じ括り方のtotalで比較する。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory AlgebraicTopology
open scoped Simplicial
universe u v w
local notation "up" => ComplexShape.up ℕ
set_option backward.isDefEq.respectTransparency false

/-- 元の二重複体の図式に自然な、同じ零次行射影。 -/
def cechIntegerRowZeroProjection {J : Type v} [Category.{w} J]
    (D : J ⥤ HomologicalComplex₂ (ModuleCat.{u} ℤ) up up) :
    D ⋙ cechIntegerLiftTotalFunctor ⟶
      D ⋙ (HomologicalComplex.eval (ModuleCat.{u} ℤ) up 0).mapHomologicalComplex up where
  app j := SerrePositivity.HomologicalAlgebra.totalToRowZero (D.obj j)
  naturality := by
    intro j k f
    exact cechIntegerTotalToRowZero_naturality (D.map f)

/-- 元の二重複体の図式に自然な、同じ零次列射影。 -/
def cechIntegerColumnZeroProjection {J : Type v} [Category.{w} J]
    (D : J ⥤ HomologicalComplex₂ (ModuleCat.{u} ℤ) up up) :
    D ⋙ cechIntegerLiftTotalFunctor ⟶
      D ⋙ HomologicalComplex.eval (CochainComplex (ModuleCat.{u} ℤ) ℕ) up 0 where
  app j := SerrePositivity.HomologicalAlgebra.totalToColumnZero (D.obj j)
  naturality := by
    intro j k f
    exact cechIntegerTotalToColumnZero_naturality (D.map f)

/-- 同じ余単体変数の各全射擬同型を、交代余面複体と同じtotalへ渡す。 -/
theorem cechIntegerCosimplicialTotal_quasiIso_of_objectwise
    {D E : SimplexCategory ⥤ CochainComplex (ModuleCat.{u} ℤ) ℕ} (φ : D ⟶ E)
    (hq : ∀ n, QuasiIso (φ.app n))
    (hs : ∀ n b, Function.Surjective (((φ.app n).f b).hom)) :
    QuasiIso (HomologicalComplex₂.total.map
      ((alternatingCofaceMapComplex (CochainComplex (ModuleCat.{u} ℤ) ℕ)).map φ) up) := by
  apply cechIntegerLiftTotal_quasiIso_of_columns
  · intro a
    exact hq ⦋a⦌
  · intro a b
    exact hs ⦋a⦌ b

/-- 各余単体で正の行が完全なら、同じ共通totalから零次行の軸への射は擬同型。 -/
theorem cechIntegerCosimplicialRowZero_quasiIso
    (D : SimplexCategory ⥤ HomologicalComplex₂ (ModuleCat.{u} ℤ) up up)
    (hD : ∀ n a b, 0 < b →
      (SerrePositivity.HomologicalAlgebra.bicomplexRow (D.obj n) b).ExactAt a) :
    QuasiIso (HomologicalComplex₂.total.map
      ((alternatingCofaceMapComplex (CochainComplex (ModuleCat.{u} ℤ) ℕ)).map
        (cechIntegerRowZeroProjection D)) up) := by
  apply cechIntegerCosimplicialTotal_quasiIso_of_objectwise
  · intro n
    exact cechIntegerTotalToRowZero_quasiIso (D.obj n) (hD n)
  · intro n b
    exact cechIntegerTotalToRowZero_component_surjective (D.obj n) b

/-- 各余単体で正の列が完全なら、同じ共通totalから零次列の軸への射は擬同型。 -/
theorem cechIntegerCosimplicialColumnZero_quasiIso
    (D : SimplexCategory ⥤ HomologicalComplex₂ (ModuleCat.{u} ℤ) up up)
    (hD : ∀ n a, 0 < a → ((D.obj n).X a).Acyclic) :
    QuasiIso (HomologicalComplex₂.total.map
      ((alternatingCofaceMapComplex (CochainComplex (ModuleCat.{u} ℤ) ℕ)).map
        (cechIntegerColumnZeroProjection D)) up) := by
  apply cechIntegerCosimplicialTotal_quasiIso_of_objectwise
  · intro n
    exact cechIntegerTotalToColumnZero_quasiIso (D.obj n) (hD n)
  · intro n b
    exact cechIntegerTotalToColumnZero_component_surjective (D.obj n) b

end SerrePositivity.AlgebraicGeometry
