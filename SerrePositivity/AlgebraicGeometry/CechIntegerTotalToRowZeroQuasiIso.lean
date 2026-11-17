module

public import SerrePositivity.AlgebraicGeometry.CechIntegerLiftTotalNaturality
public import SerrePositivity.AlgebraicGeometry.CechIntegerLiftTotal
public import SerrePositivity.HomologicalAlgebra.BicomplexRowQuasiIso
import all SerrePositivity.HomologicalAlgebra.BicomplexProjection

/-!
概要：元の零次行射影の自然性と全射性を保ち、既存のHAの擬同型を整数係数へ渡す。
方針：同じ直和入射と既存の係数の同値を使う。
規約：HAの型を変更せず、対角線消去を再実装しない。
使われ方：相対の二つの増大Čechの比較を共通のtotalから軸へ渡す。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory CategoryTheory.Limits
universe u
local notation "up" => ComplexShape.up ℕ
variable {K L : HomologicalComplex₂ (ModuleCat.{u} ℤ) up up}

set_option backward.isDefEq.respectTransparency false in
/-- 同じ零次行射影は元の二重複体の射に自然。 -/
theorem cechIntegerTotalToRowZero_naturality (f : K ⟶ L) :
    HomologicalComplex₂.total.map f up ≫ SerrePositivity.HomologicalAlgebra.totalToRowZero L =
      SerrePositivity.HomologicalAlgebra.totalToRowZero K ≫
        ((HomologicalComplex.eval (ModuleCat.{u} ℤ) up 0).mapHomologicalComplex up).map f := by
  apply HomologicalComplex.Hom.ext
  funext n
  simp only [HomologicalComplex.comp_f]
  apply HomologicalComplex₂.total.hom_ext
  intro a b h
  rw [← Category.assoc, HomologicalComplex₂.ιTotal_map, Category.assoc]
  by_cases hb : b = 0
  · subst b
    have ha : a = n := by simpa using h
    subst a
    simp [SerrePositivity.HomologicalAlgebra.totalToRowZero,
      SerrePositivity.HomologicalAlgebra.rowZeroApp]
  · simp [SerrePositivity.HomologicalAlgebra.totalToRowZero,
      SerrePositivity.HomologicalAlgebra.rowZeroApp, hb]

set_option backward.isDefEq.respectTransparency false in
/-- 元の各全次数の零次行射影は、元の軸入射を右逆として持つので全射。 -/
theorem cechIntegerTotalToRowZero_component_surjective (K : HomologicalComplex₂ (ModuleCat.{u} ℤ) up up)
    (n : ℕ) : Function.Surjective
      ((SerrePositivity.HomologicalAlgebra.totalToRowZero K).f n).hom := by
  intro x
  refine ⟨(K.ιTotal up n 0 n (by change n + 0 = n; omega)).hom x, ?_⟩
  have hi : K.ιTotal up n 0 n (by change n + 0 = n; omega) ≫
      (SerrePositivity.HomologicalAlgebra.totalToRowZero K).f n = 𝟙 _ := by
    simp [SerrePositivity.HomologicalAlgebra.totalToRowZero,
      SerrePositivity.HomologicalAlgebra.rowZeroApp]
  exact congrArg (fun v ↦ v.hom x) hi

set_option backward.isDefEq.respectTransparency false in
/-- 正の行が完全なら元の同じ零次行射影は擬同型。既存HAの判定の係数移送。 -/
theorem cechIntegerTotalToRowZero_quasiIso (K : HomologicalComplex₂ (ModuleCat.{u} ℤ) up up)
    (hK : ∀ a b, 0 < b → (SerrePositivity.HomologicalAlgebra.bicomplexRow K b).ExactAt a) :
    QuasiIso (SerrePositivity.HomologicalAlgebra.totalToRowZero K) := by
  let π := SerrePositivity.HomologicalAlgebra.totalToRowZero K
  let M := cechIntegerLiftBicomplex K
  let πM := SerrePositivity.HomologicalAlgebra.totalToRowZero M
  have hM : ∀ a b, 0 < b → (SerrePositivity.HomologicalAlgebra.bicomplexRow M b).ExactAt a := by
    intro a b hb
    exact (cechIntegerLiftComplex_exactAt_iff
      (SerrePositivity.HomologicalAlgebra.bicomplexRow K b) a).mpr (hK a b hb)
  have hq : QuasiIso πM := SerrePositivity.HomologicalAlgebra.totalToRowZero_quasiIso M hM
  have hc : (cechIntegerLiftTotalIso K).hom ≫
      (cechIntegerLiftFunctor.mapHomologicalComplex up).map π = πM := by
    apply HomologicalComplex.Hom.ext
    funext n
    change (cechIntegerLiftTotalComponentIso K n).hom ≫ cechIntegerLiftFunctor.map (π.f n) = πM.f n
    apply HomologicalComplex₂.total.hom_ext
    intro a b h
    rw [← Category.assoc, cechIntegerLiftTotalComponentIso_ι, ← Functor.map_comp]
    by_cases hb : b = 0
    · subst b
      have ha : a = n := by simpa using h
      subst a
      simp [π, πM, M, SerrePositivity.HomologicalAlgebra.totalToRowZero,
        SerrePositivity.HomologicalAlgebra.rowZeroApp]
    · simp [π, πM, M, SerrePositivity.HomologicalAlgebra.totalToRowZero,
        SerrePositivity.HomologicalAlgebra.rowZeroApp, hb]
  have hF : QuasiIso ((cechIntegerLiftFunctor.mapHomologicalComplex up).map π) := by
    apply (_root_.quasiIso_iff_comp_left (cechIntegerLiftTotalIso K).hom _).mp
    rw [hc]
    exact hq
  exact (HomologicalComplex.quasiIso_map_iff_of_preservesHomology π cechIntegerLiftFunctor).mp hF

end SerrePositivity.AlgebraicGeometry
