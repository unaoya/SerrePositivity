module

public import SerrePositivity.AlgebraicGeometry.ProjectiveCechFunctor
public import Mathlib.Algebra.Homology.Linear
public import Mathlib.Algebra.Homology.ShortComplex.Linear
public import Mathlib.CategoryTheory.Linear.FunctorCategory

/-!
概要：Čech 版のコホモロジーで、係数写像のスカラー倍を追跡する。
方針：係数の自然変換のスカラー倍を複体へ移し、短複体の既存の線形性を使う。
規約：被覆と係数環を固定する。
使われ方：原典 Stacks 30.20.1 の Hⁱ に対応する Čech 版の Rees 比較とスカラー作用。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory

universe u
variable {B : Type u} [CommRing B] {ι : Type} [DecidableEq ι]
variable {D E : Finset ι ⥤ ModuleCat.{u} B}

/-- Čech 複体への係数写像の構成は、スカラー倍を保つ。 -/
theorem projectiveCechComplexMap_smul (b : B) (η : D ⟶ E) :
    fullCechComplexMap (b • η) = b • fullCechComplexMap η := by
  ext q x
  rfl

/-- Čech 版のコホモロジー写像は、係数写像のスカラー倍を保つ。
原典 Stacks 30.20.1 の Hⁱ と Rees 作用に対応する Čech 版の補題。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。 -/
theorem projectiveCechHomologyMap_smul (b : B) (η : D ⟶ E) (q : ℕ) :
    HomologicalComplex.homologyMap (fullCechComplexMap (b • η)) q =
      b • HomologicalComplex.homologyMap (fullCechComplexMap η) q := by
  rw [projectiveCechComplexMap_smul]
  change ShortComplex.homologyMap (b •
    ((HomologicalComplex.shortComplexFunctor (ModuleCat.{u} B) (.up ℕ) q).map
      (fullCechComplexMap η))) = _
  exact ShortComplex.homologyMap_smul
    ((HomologicalComplex.shortComplexFunctor (ModuleCat.{u} B) (.up ℕ) q).map
      (fullCechComplexMap η)) b

/-- Čech 版のコホモロジーで、恒等係数写像のスカラー倍は元のスカラー作用を誘導する。
原典 Stacks 30.20.1 の Hⁱ の Rees 作用に対応する Čech 版の式。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。 -/
theorem projectiveCechHomologyMap_smul_id (b : B) (D : Finset ι ⥤ ModuleCat.{u} B) (q : ℕ) :
    HomologicalComplex.homologyMap (fullCechComplexMap (b • 𝟙 D)) q =
      b • 𝟙 ((fullCechComplex D).homology q) := by
  rw [projectiveCechHomologyMap_smul]
  rw [show fullCechComplexMap (𝟙 D) = 𝟙 (fullCechComplex D) from
    (fullCechComplexFunctor (R := B) (ι := ι)).map_id D]
  rw [HomologicalComplex.homologyMap_id]

end SerrePositivity.AlgebraicGeometry
