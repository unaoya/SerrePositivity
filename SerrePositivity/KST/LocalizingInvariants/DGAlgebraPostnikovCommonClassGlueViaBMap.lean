module

public import
  SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonClassGlueStandardBottom

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreClassGlueViaBMap
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreSpecialization

/-!
概要：元の分母比較の右辺の零底像を、同じ G⁻¹・ViaB・W の実合成へ同定する。
方針：底付き移送の反転保存と二回の合成保存を、全経路の等式として使う。
規約：元の G・W と係数射を保持。使われ方：分母比較と native 標準比較の縦合成。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
open ProExcision
variable (R : Type u) [CommRing R] {A B : Tower (NonpositiveAlgebra R)} (f : LevelHom A B)
  {i m : ℕ} {hi : i ≤ m} (c : NonpositiveInverseRoof R (f.map (postnikovFunctor R 1)) i m hi)
  (d : PostnikovCommonLayerInverse R f c) {j : ℕ} (hj : j ≤ i)

def postnikovCommonClassGlueSolvedMappedPath :=
  PostnikovCommonCore.postnikovCommonClassGlueSolvedMappedPath
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj)

lemma postnikovCommonClassGlueViaB_map_hom :
    (postnikovCommonClassGlueSolvedMappedPath R f c d hj).hom =
      (postnikovCommonClassGlueViaBBottom R f c d hj).hom :=
  PostnikovCommonCore.postnikovCommonClassGlueViaB_map_hom
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
