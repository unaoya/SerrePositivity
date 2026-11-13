module

public import SerrePositivity.AlgebraicGeometry.ProjectiveCechIntFiltered
public import Mathlib.CategoryTheory.Limits.Final
public import Mathlib.CategoryTheory.Category.ULift

/-!
概要：自然数の整数係数図式について、Čech H と順極限を自然に比較する。
方針：添字を同値な AsSmall ℕ へ移し、filtered 余極限の既存比較を使う。
規約：添字の宇宙を加群の宇宙へ移すだけで、有限段の写像は変えない。
使われ方：F6 の実際の Frobenius 系の Čech H の比較。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
universe u
variable {ι : Type} [DecidableEq ι] [Fintype ι]

/-- 自然数の整数係数 Čech H と順極限の自然同型。
BST13 Lemma 3.9 の Hⁱ の Frobenius 極限に用いる Čech 版。分離的なスキームの
準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、この比較は形式化しない。 -/
def projectiveIntCechSequentialHomologyNatIso (q : ℕ) :
    colim (J := ℕ) ⋙ (fullCechComplexFunctor (R := ℤ) (ι := ι) ⋙
      HomologicalComplex.homologyFunctor (ModuleCat.{u} ℤ) (.up ℕ) q) ≅
    (whiskeringRight ℕ (Finset ι ⥤ ModuleCat.{u} ℤ) (ModuleCat.{u} ℤ)).obj
      (fullCechComplexFunctor ⋙
        HomologicalComplex.homologyFunctor (ModuleCat.{u} ℤ) (.up ℕ) q) ⋙ colim := by
  let e : AsSmall.{u} ℕ ≌ ℕ := AsSmall.equiv.symm
  let H := fullCechComplexFunctor (R := ℤ) (ι := ι) ⋙
    HomologicalComplex.homologyFunctor (ModuleCat.{u} ℤ) (.up ℕ) q
  let pre := (whiskeringLeft _ _ (Finset ι ⥤ ModuleCat.{u} ℤ)).obj e.functor
  exact isoWhiskerRight (Final.colimIso e.functor).symm H ≪≫
    isoWhiskerLeft pre (projectiveIntCechFilteredHomologyNatIso (J := AsSmall.{u} ℕ) q) ≪≫
    isoWhiskerLeft ((whiskeringRight ℕ _ _).obj H) (Final.colimIso e.functor)

/-- 自然数で添字付けした係数図式ごとの Čech H の順極限同型。 -/
def projectiveIntCechSequentialHomologyIso
    (D : ℕ ⥤ Finset ι ⥤ ModuleCat.{u} ℤ) (q : ℕ) :
    (fullCechComplex (colimit D)).homology q ≅
      colimit (D ⋙ fullCechComplexFunctor ⋙
        HomologicalComplex.homologyFunctor (ModuleCat.{u} ℤ) (.up ℕ) q) :=
  (projectiveIntCechSequentialHomologyNatIso q).app D

/-- 順極限の Čech H の比較は実際の係数系の射に自然。 -/
theorem projectiveIntCechSequentialHomologyIso_naturality
    {D E : ℕ ⥤ Finset ι ⥤ ModuleCat.{u} ℤ} (η : D ⟶ E) (q : ℕ) :
    (fullCechComplexFunctor ⋙
        HomologicalComplex.homologyFunctor (ModuleCat.{u} ℤ) (.up ℕ) q).map (colim.map η) ≫
        (projectiveIntCechSequentialHomologyIso E q).hom =
      (projectiveIntCechSequentialHomologyIso D q).hom ≫
        colim.map (whiskerRight η (fullCechComplexFunctor ⋙
          HomologicalComplex.homologyFunctor (ModuleCat.{u} ℤ) (.up ℕ) q)) :=
  (projectiveIntCechSequentialHomologyNatIso q).hom.naturality η

end SerrePositivity.AlgebraicGeometry
