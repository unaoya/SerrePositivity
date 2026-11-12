module

public import SerrePositivity.AlgebraicGeometry.ProjectiveCechSemilinearMap

/-!
概要：半線形な係数図式の可換四角形を Čech コホモロジーへ送る。
方針：係数制限のコホモロジー比較の自然性と、全タプル Čech 関手の合成則を使う。
規約：半線形性を係数環の準同型として固定する。
使われ方：Frobenius と閉厚化の射・I 進遷移との整合性。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory
universe u
variable {R B : Type u} [CommRing R] [CommRing B]
variable {ι : Type} [DecidableEq ι]
variable (φ : R →+* B)
variable {D D' : Finset ι ⥤ ModuleCat.{u} R}
variable {E E' : Finset ι ⥤ ModuleCat.{u} B}

/-- 半線形な係数の可換四角形は、Čech H の同じ四角形を与える。
原典 BS17 Lemma 4.6(i) の Hⁱ と Frobenius に使う Čech 版の自然性。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。 -/
theorem projectiveCechSemilinearHomologyMap_naturality
    (η : D ⟶ E ⋙ ModuleCat.restrictScalars φ)
    (η' : D' ⟶ E' ⋙ ModuleCat.restrictScalars φ)
    (f : D ⟶ D') (g : E ⟶ E')
    (h : f ≫ η' = η ≫ Functor.whiskerRight g (ModuleCat.restrictScalars φ))
    (q : ℕ) (x : (fullCechComplex D).homology q) :
    projectiveCechSemilinearHomologyMap φ D' E' η' q
        (((HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (.up ℕ) q).map
          (fullCechComplexMap f)).hom x) =
      ((HomologicalComplex.homologyFunctor (ModuleCat.{u} B) (.up ℕ) q).map
          (fullCechComplexMap g)).hom
        (projectiveCechSemilinearHomologyMap φ D E η q x) := by
  let H : (Finset ι ⥤ ModuleCat.{u} R) ⥤ ModuleCat.{u} R := fullCechComplexFunctor ⋙
    HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (.up ℕ) q
  let HB : (Finset ι ⥤ ModuleCat.{u} B) ⥤ ModuleCat.{u} B := fullCechComplexFunctor ⋙
    HomologicalComplex.homologyFunctor (ModuleCat.{u} B) (.up ℕ) q
  have hh : H.map f ≫ H.map η' ≫ (projectiveCechRestrictScalarsHomologyIso φ E' q).hom =
      H.map η ≫ (projectiveCechRestrictScalarsHomologyIso φ E q).hom ≫
        (ModuleCat.restrictScalars φ).map (HB.map g) := by
    rw [← H.map_comp_assoc, h, H.map_comp_assoc]
    exact congrArg (fun k ↦ H.map η ≫ k)
      (projectiveCechRestrictScalarsHomologyIso_naturality φ g q)
  exact congrArg (fun k ↦ k.hom x) hh

end SerrePositivity.AlgebraicGeometry
