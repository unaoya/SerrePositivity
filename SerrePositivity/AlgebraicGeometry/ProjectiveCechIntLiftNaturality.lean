module

public import SerrePositivity.AlgebraicGeometry.ProjectiveCechIntLift

/-!
概要：整数係数の宇宙移送と Čech H の比較を、係数図式の射に自然にする。
方針：係数を往復する恒等同型と、整数への係数制限の自然性を合成する。
規約：同じ標準開の有限交叉の添字を使う。
使われ方：2e の filtered 余極限比較を移送し、閉厚化の制限を保つ。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory CategoryTheory.Functor
universe u
variable {ι : Type} [DecidableEq ι]

/-- 整数係数の図式を ULift ℤ の図式へ移す関手。 -/
abbrev projectiveIntCechLiftFunctor :
    (Finset ι ⥤ ModuleCat.{u} ℤ) ⥤ (Finset ι ⥤ ModuleCat.{u} (ULift.{u} ℤ)) :=
  (whiskeringRight _ _ _).obj
    (ModuleCat.restrictScalars (ULift.ringEquiv.toRingHom : ULift.{u} ℤ →+* ℤ))

/-- 係数の往復同型の逆は係数図式の射に自然。 -/
theorem projectiveIntCechLiftRoundtripIso_inv_naturality
    {D E : Finset ι ⥤ ModuleCat.{u} ℤ} (η : D ⟶ E) :
    η ≫ (projectiveIntCechLiftRoundtripIso E).inv =
      (projectiveIntCechLiftRoundtripIso D).inv ≫
        Functor.whiskerRight (projectiveIntCechLiftFunctor.map η)
          (ModuleCat.restrictScalars (Int.castRingHom (ULift.{u} ℤ))) := by
  ext T x
  rfl

/-- ULift ℤ への Čech H の移送は係数図式の射に自然。
BST13 Lemma 3.9 の Hⁱ に用いる Čech 版。分離的なスキームの準連接層では
アフィン被覆の Čech と一致する（Stacks 30.2.6）が、この比較は形式化しない。 -/
theorem projectiveIntCechLiftHomologyIso_naturality
    {D E : Finset ι ⥤ ModuleCat.{u} ℤ} (η : D ⟶ E) (q : ℕ) :
    (fullCechComplexFunctor ⋙
        HomologicalComplex.homologyFunctor (ModuleCat.{u} ℤ) (.up ℕ) q).map η ≫
        (projectiveIntCechLiftHomologyIso E q).hom =
      (projectiveIntCechLiftHomologyIso D q).hom ≫
        (ModuleCat.restrictScalars (Int.castRingHom (ULift.{u} ℤ))).map
          ((fullCechComplexFunctor ⋙
            HomologicalComplex.homologyFunctor (ModuleCat.{u} (ULift.{u} ℤ)) (.up ℕ) q).map
              (projectiveIntCechLiftFunctor.map η)) := by
  let H := fullCechComplexFunctor (ι := ι) ⋙
    HomologicalComplex.homologyFunctor (ModuleCat.{u} ℤ) (.up ℕ) q
  change H.map η ≫ H.map (projectiveIntCechLiftRoundtripIso E).inv ≫
      (projectiveCechIntRestrictionHomologyIso (projectiveIntCechLiftDiagram E) q).hom =
    (H.map (projectiveIntCechLiftRoundtripIso D).inv ≫
      (projectiveCechIntRestrictionHomologyIso (projectiveIntCechLiftDiagram D) q).hom) ≫ _
  rw [← H.map_comp_assoc, projectiveIntCechLiftRoundtripIso_inv_naturality,
    H.map_comp_assoc]
  have h := projectiveCechIntRestrictionHomologyIso_naturality
    (projectiveIntCechLiftFunctor.map η) q
  have hh := congrArg
    (fun k ↦ H.map (projectiveIntCechLiftRoundtripIso D).inv ≫ k) h
  exact hh

/-- 整数係数の Čech H を同じ宇宙の係数環で計算する自然同型。 -/
def projectiveIntCechLiftHomologyNatIso (q : ℕ) :
    fullCechComplexFunctor (ι := ι) ⋙
        HomologicalComplex.homologyFunctor (ModuleCat.{u} ℤ) (.up ℕ) q ≅
      projectiveIntCechLiftFunctor ⋙ fullCechComplexFunctor ⋙
        HomologicalComplex.homologyFunctor (ModuleCat.{u} (ULift.{u} ℤ)) (.up ℕ) q ⋙
          ModuleCat.restrictScalars (Int.castRingHom (ULift.{u} ℤ)) :=
  NatIso.ofComponents (fun D ↦ projectiveIntCechLiftHomologyIso D q)
    (fun η ↦ projectiveIntCechLiftHomologyIso_naturality η q)

end SerrePositivity.AlgebraicGeometry
