module

public import SerrePositivity.AlgebraicGeometry.ProjectiveCechFilteredCochains
public import SerrePositivity.AlgebraicGeometry.ProjectiveFilteredHomology

/-!
概要：有限被覆の全タプル Čech 複体とその H は filtered 余極限と交換する。
方針：有限な各項の比較と、加群の filtered 余極限の完全性を合成する。
規約：基底を固定した加群の比較。動く基底の標準開との接続は別に行う。
使われ方：射影の場合の Noether 近似の Čech 計算。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory CategoryTheory.Limits
universe u
variable {R : Type u} [CommRing R] {ι : Type} [DecidableEq ι] [Fintype ι]
variable {J : Type u} [SmallCategory J] [IsFiltered J]

/-- 有限被覆の全タプル Čech 複体は filtered 余極限を保つ。 -/
instance projectiveFullCechFunctorPreservesFilteredColimits :
    PreservesColimitsOfShape J
      (fullCechComplexFunctor : (Finset ι ⥤ ModuleCat.{u} R) ⥤
        CochainComplex (ModuleCat.{u} R) ℕ) := by
  apply HomologicalComplex.preservesColimitsOfShape_of_eval
  intro q
  apply preservesColimitsOfShape_of_natIso
    (F := projectiveCechCochainsFunctor (R := R) (ι := ι) (q + 1))
  exact NatIso.ofComponents (fun _ ↦ Iso.refl _) (by intros; rfl)

/-- 有限被覆の Čech 複体と係数図式の filtered 余極限との canonical な比較。 -/
def projectiveCechFilteredComplexIso (D : J ⥤ Finset ι ⥤ ModuleCat.{u} R) :
    fullCechComplex (colimit D) ≅ colimit (D ⋙ fullCechComplexFunctor) :=
  preservesColimitIso (fullCechComplexFunctor (R := R) (ι := ι)) D

/-- 有限被覆の Čech H は、係数図式の filtered 余極限と交換する。
原典 Stacks 30.6.1 の Hⁱ の極限比較に対応する Čech 版。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。 -/
def projectiveCechFilteredHomologyIso (D : J ⥤ Finset ι ⥤ ModuleCat.{u} R) (q : ℕ) :
    (fullCechComplex (colimit D)).homology q ≅
      colimit (D ⋙ fullCechComplexFunctor ⋙
        HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (.up ℕ) q) :=
  (HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (.up ℕ) q).mapIso
      (projectiveCechFilteredComplexIso D) ≪≫
    projectiveFilteredComplexHomologyIso (D ⋙ fullCechComplexFunctor) q

end SerrePositivity.AlgebraicGeometry
