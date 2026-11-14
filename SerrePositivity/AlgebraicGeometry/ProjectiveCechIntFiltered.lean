module

public import SerrePositivity.AlgebraicGeometry.ProjectiveCechIntLiftNaturality
public import SerrePositivity.AlgebraicGeometry.ProjectiveCechFilteredNaturality
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic

/-!
概要：任意の宇宙の整数加群の Čech H と filtered 余極限を自然に比較する。
方針：ULift ℤ へ移し、2e の既存比較を使って整数へ戻す。
規約：filtered 余極限と H の交換を再証明せず、係数移送と自然同型を合成する。
使われ方：F6 の Frobenius 順極限を係数の perfection の Čech H へ接続する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
universe u
variable {ι : Type} [DecidableEq ι] [Fintype ι]
variable {J : Type u} [SmallCategory J] [IsFiltered J]

/-- 2e の filtered 余極限と Čech H の比較を自然同型としてまとめる。 -/
def projectiveCechFilteredHomologyNatIso {R : Type u} [CommRing R] (q : ℕ) :
    colim (J := J) ⋙ (fullCechComplexFunctor (R := R) (ι := ι) ⋙
      HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (.up ℕ) q) ≅
    (whiskeringRight J (Finset ι ⥤ ModuleCat.{u} R) (ModuleCat.{u} R)).obj
      (fullCechComplexFunctor ⋙
        HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (.up ℕ) q) ⋙ colim :=
  NatIso.ofComponents (fun D ↦ projectiveCechFilteredHomologyIso D q)
    (fun η ↦ projectiveCechFilteredHomologyIso_naturality η q)

/-- 整数係数の Čech H の filtered 余極限比較。
BST13 Lemma 3.9 の Hⁱ の Frobenius 極限に用いる Čech 版。分離的なスキームの
準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、この比較は形式化しない。 -/
def projectiveIntCechFilteredHomologyNatIso (q : ℕ) :
    colim (J := J) ⋙ (fullCechComplexFunctor (R := ℤ) (ι := ι) ⋙
      HomologicalComplex.homologyFunctor (ModuleCat.{u} ℤ) (.up ℕ) q) ≅
    (whiskeringRight J (Finset ι ⥤ ModuleCat.{u} ℤ) (ModuleCat.{u} ℤ)).obj
      (fullCechComplexFunctor ⋙
        HomologicalComplex.homologyFunctor (ModuleCat.{u} ℤ) (.up ℕ) q) ⋙ colim := by
  let L := projectiveIntCechLiftFunctor.{u} (ι := ι)
  let H := fullCechComplexFunctor (R := ULift.{u} ℤ) (ι := ι) ⋙
    HomologicalComplex.homologyFunctor (ModuleCat.{u} (ULift.{u} ℤ)) (.up ℕ) q
  let U := ModuleCat.restrictScalars (Int.castRingHom (ULift.{u} ℤ))
  let postL := (whiskeringRight J _ _).obj L
  let postH := (whiskeringRight J _ _).obj H
  let e := projectiveIntCechLiftHomologyNatIso.{u} (ι := ι) q
  exact isoWhiskerLeft colim e ≪≫
    isoWhiskerRight (preservesColimitNatIso L) (H ⋙ U) ≪≫
    isoWhiskerRight
      (isoWhiskerLeft postL (projectiveCechFilteredHomologyNatIso (J := J)
        (R := ULift.{u} ℤ) (ι := ι) q)) U ≪≫
    isoWhiskerLeft (postL ⋙ postH) (preservesColimitNatIso U) ≪≫
    isoWhiskerRight ((whiskeringRight J _ _).mapIso e).symm colim

/-- 整数係数の図式ごとの Čech H の filtered 余極限同型。 -/
def projectiveIntCechFilteredHomologyIso
    (D : J ⥤ Finset ι ⥤ ModuleCat.{u} ℤ) (q : ℕ) :
    (fullCechComplex (colimit D)).homology q ≅
      colimit (D ⋙ fullCechComplexFunctor ⋙
        HomologicalComplex.homologyFunctor (ModuleCat.{u} ℤ) (.up ℕ) q) :=
  (projectiveIntCechFilteredHomologyNatIso q).app D

end SerrePositivity.AlgebraicGeometry
