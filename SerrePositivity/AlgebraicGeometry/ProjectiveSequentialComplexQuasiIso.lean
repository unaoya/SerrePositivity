module

public import SerrePositivity.AlgebraicGeometry.ProjectiveFilteredComplexQuasiIso
public import Mathlib.CategoryTheory.Limits.Final
public import Mathlib.CategoryTheory.Category.ULift

/-!
概要：各有限段の Čech 比較の同型性を、自然数の順極限へ渡す。
方針：AsSmall ℕ への終関手による添字の移送と filtered 比較を合成する。
規約：加群の宇宙を自然数の宇宙に制限しない。
使われ方：Frobenius 後の共通アフィン細分の準同型。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
universe u v
variable {R : Type v} [CommRing R]
variable {F G : ℕ ⥤ CochainComplex (ModuleCat.{u} R) ℕ}

/-- 各段で次数 q の H に同型を誘導する射は、自然数の順極限でもそうなる。 -/
theorem projectiveSequentialComplexMap_quasiIsoAt (η : F ⟶ G) (q : ℕ)
    (hη : ∀ n, QuasiIsoAt (η.app n) q) : QuasiIsoAt (colim.map η) q := by
  let e : AsSmall.{u} ℕ ≌ ℕ := AsSmall.equiv.symm
  let η' := whiskerLeft e.functor η
  haveI : QuasiIsoAt (colim.map η') q :=
    projectiveFilteredComplexMap_quasiIsoAt η' q (fun j ↦ hη (e.functor.obj j))
  let a := (Final.colimIso e.functor (E := CochainComplex (ModuleCat.{u} R) ℕ)).app F
  let b := (Final.colimIso e.functor (E := CochainComplex (ModuleCat.{u} R) ℕ)).app G
  have h : colim.map η' ≫ b.hom = a.hom ≫ colim.map η :=
    (Final.colimIso e.functor).hom.naturality η
  haveI : QuasiIsoAt (a.hom ≫ colim.map η) q := by
    rw [← h]
    infer_instance
  exact quasiIsoAt_of_comp_left a.hom (colim.map η) q

/-- 各有限段の quasi-isomorphism は、自然数の順極限でも quasi-isomorphism。 -/
theorem projectiveSequentialComplexMap_quasiIso (η : F ⟶ G)
    [∀ n, QuasiIso (η.app n)] : QuasiIso (colim.map η) where
  quasiIsoAt q := projectiveSequentialComplexMap_quasiIsoAt η q (fun _ ↦ inferInstance)

end SerrePositivity.AlgebraicGeometry
