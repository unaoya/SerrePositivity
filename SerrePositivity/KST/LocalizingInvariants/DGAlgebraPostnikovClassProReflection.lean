module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraNormalizedClassDerivedPro
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovBoundedDerivedPro

/-!
概要：元の class 模型の実 pro 逆を、元の有限切断と有界な元の源射へ反映する。
方針：元の準同型比較と商射の自然性の正方形を各段の可逆射として反映する。
規約：一般の pro ∞ 同値とは同一視しない。使われ方：n=1 の実局所化 pro 逆。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
open ProExcision
variable (R : Type u) [CommRing R] {A B : Tower (NonpositiveAlgebra R)} (f : LevelHom A B)
  {D : Type v} [Category.{w} D] (L : Mon (Complex R) ⥤ D)

lemma postnikovClassModelMap_reflects_proIso (hL : InvertsQuasiIsos R L)
    (n : ℤ) (hn : 0 ≤ n)
    (hf : IsProIso ((f.map (postnikovClassModelFunctor R n hn)).map L)) :
    IsProIso ((f.map (postnikovFunctor R (n + 1))).map L) := by
  let a := (TowerDiagram.mapNat A (postnikovClassModelComparison R n hn)).map L
  let b := (TowerDiagram.mapNat B (postnikovClassModelComparison R n hn)).map L
  have : ∀ i, IsIso (a.app i) := fun i => hL _
    (postnikovClassModelComparison_quasiIso R n hn (A.obj i))
  have : ∀ i, IsIso (b.app i) := fun i => hL _
    (postnikovClassModelComparison_quasiIso R n hn (B.obj i))
  apply TowerDiagram.proIso_of_square_reverse _ _ a b ?_ hf
  apply ProSpectrum.levelHom_ext
  intro i
  change L.map (postnikovMap R (f.app i).hom (n + 1)) ≫
      L.map (postnikovHomotopyPullbackComparison R (B.obj i).obj n hn) =
    L.map (postnikovHomotopyPullbackComparison R (A.obj i).obj n hn) ≫
      L.map (postnikovClassModelMap R n hn (f.app i).hom)
  rw [← L.map_comp, ← L.map_comp]
  exact congrArg L.map (postnikovHomotopyPullbackComparison_square R n hn (f.app i).hom)

lemma postnikovMap_reflects_proIso_of_bounded (hL : InvertsQuasiIsos R L) (n : ℤ)
    (hA : ∀ i, (A.obj i).obj.X.IsGE (-n)) (hB : ∀ i, (B.obj i).obj.X.IsGE (-n))
    (hf : IsProIso ((f.map (postnikovFunctor R n)).map L)) :
    IsProIso ((f.map (nonpositiveInclusion R)).map L) := by
  let a := (TowerDiagram.mapNat A (postnikovQuotientNatTrans R n)).map L
  let b := (TowerDiagram.mapNat B (postnikovQuotientNatTrans R n)).map L
  have : ∀ i, IsIso (a.app i) := fun i => hL _
    (postnikovQuotient_quasiIso R (A.obj i).obj n (hA i))
  have : ∀ i, IsIso (b.app i) := fun i => hL _
    (postnikovQuotient_quasiIso R (B.obj i).obj n (hB i))
  apply TowerDiagram.proIso_of_square_reverse _ _ a b ?_ hf
  apply ProSpectrum.levelHom_ext
  intro i
  change L.map (f.app i).hom ≫ L.map (postnikovQuotient R (B.obj i).obj n) =
    L.map (postnikovQuotient R (A.obj i).obj n) ≫ L.map (postnikovMap R (f.app i).hom n)
  rw [← L.map_comp, ← L.map_comp]
  exact congrArg L.map (postnikovQuotient_naturality R (f.app i).hom n).symm

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
