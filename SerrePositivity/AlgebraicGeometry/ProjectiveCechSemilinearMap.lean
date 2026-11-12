module

public import SerrePositivity.AlgebraicGeometry.ProjectiveCechRestrictScalarsNaturality

/-!
概要：半線形な係数図式の写像を、Čech コホモロジーの半線形写像にする。
方針：変更先の係数作用を制限して線形な自然変換とし、既存の係数制限比較を使う。
規約：元の係数作用と制限した作用を ModuleCat で区別する。
使われ方：実際の Frobenius の標準開の写像を I 進系と形式関数の半線形な自然性へ渡す。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory
universe u
variable {R B : Type u} [CommRing R] [CommRing B]
variable {ι : Type} [DecidableEq ι]
variable (φ : R →+* B)
variable (D : Finset ι ⥤ ModuleCat.{u} R) (E : Finset ι ⥤ ModuleCat.{u} B)

/-- 係数制限として与えた図式の写像は、Čech コホモロジーの半線形写像を誘導する。
原典 BS17 Lemma 4.6(i) の Hⁱ と Frobenius の整合性に使う Čech 版。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。 -/
def projectiveCechSemilinearHomologyMap
    (η : D ⟶ E ⋙ ModuleCat.restrictScalars φ) (q : ℕ) :
    (fullCechComplex D).homology q →ₛₗ[φ] (fullCechComplex E).homology q := by
  let h := ((HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (.up ℕ) q).map
      (fullCechComplexMap η) ≫ (projectiveCechRestrictScalarsHomologyIso φ E q).hom).hom
  exact
    { toFun := h
      map_add' := h.map_add
      map_smul' r x := h.map_smul r x }

end SerrePositivity.AlgebraicGeometry
