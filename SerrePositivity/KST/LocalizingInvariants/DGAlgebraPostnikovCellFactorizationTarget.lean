module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCellLiftFactorization
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraCellAugmentation

/-!
概要：二因子分解によらない Postnikov class 比較の両端と底への四重 cell 射影。
方針：元の合成射 h だけで両端を定義し、摂動射と class 射の射影を照合する。
規約：共通底 P と元の底射 b を固定する。使われ方：同じ相対模型上の二重比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
variable (R : Type u) [CommRing R] (B D P : Mon (Complex R))
  [B.X.IsStrictlyLE 0] [D.X.IsStrictlyLE 0]
  (n : ℤ) (hn : 0 ≤ n) (b : P ⟶ postnikov R B n) (h : B ⟶ D)

def postnikovCellFactorizationProjection : cellResolution R (cellResolution R
    (cellResolution R (cellResolution R P))) ⟶ P :=
  cellAugmentation R (cellResolution R (cellResolution R (cellResolution R P))) ≫
    cellAugmentation R (cellResolution R (cellResolution R P)) ≫
    cellAugmentation R (cellResolution R P) ≫ cellAugmentation R P

lemma postnikovCellFactorizationProjection_quasiIso :
    QuasiIso (postnikovCellFactorizationProjection R P).hom := by
  simp only [postnikovCellFactorizationProjection, Mon.comp_hom']
  exact quasiIso_comp _ _
    (hφ := cellAugmentation_quasiIso R (cellResolution R (cellResolution R (cellResolution R P))))
    (hφ' := quasiIso_comp _ _
      (hφ := cellAugmentation_quasiIso R (cellResolution R (cellResolution R P)))
      (hφ' := quasiIso_comp _ _ (hφ := cellAugmentation_quasiIso R (cellResolution R P))
        (hφ' := cellAugmentation_quasiIso R P)))

lemma postnikovCellFactorizationProjection_surjective (k : ℤ) :
    Function.Surjective ((postnikovCellFactorizationProjection R P).hom.f k) := by
  exact (cellAugmentation_surjective R P k).comp
    ((cellAugmentation_surjective R (cellResolution R P) k).comp
      ((cellAugmentation_surjective R (cellResolution R (cellResolution R P)) k).comp
        (cellAugmentation_surjective R
          (cellResolution R (cellResolution R (cellResolution R P))) k)))

lemma postnikovCellFactorization_base :
    cellAugmentation R (cellResolution R (cellResolution R (cellResolution R P))) ≫
      (cellAugmentation R (cellResolution R (cellResolution R P)) ≫
        (cellAugmentation R (cellResolution R P) ≫
          postnikovCellLiftOverSource R B D P n hn b h)) ≫
      postnikovPerturbedProjection R D n hn =
    postnikovCellFactorizationProjection R P ≫ (b ≫ postnikovMap R h n) := by
  have hb := congrArg (fun t =>
    cellAugmentation R (cellResolution R (cellResolution R (cellResolution R P))) ≫
    cellAugmentation R (cellResolution R (cellResolution R P)) ≫
    cellAugmentation R (cellResolution R P) ≫ t)
    (postnikovCellLiftOverSource_projection R B D P n hn b h)
  simpa only [Category.assoc, postnikovCellFactorizationProjection] using hb

def postnikovCellFactorizationSource : cellResolution R (cellResolution R
    (cellResolution R (cellResolution R P))) ⟶ postnikovDerivationTarget R D n hn :=
  cellAugmentation R (cellResolution R (cellResolution R (cellResolution R P))) ≫
    (cellAugmentation R (cellResolution R (cellResolution R P)) ≫
      (cellAugmentation R (cellResolution R P) ≫ postnikovCellLiftOverSource R B D P n hn b h)) ≫
    postnikovPerturbedClass R D n hn

def postnikovCellFactorizationTarget : cellResolution R (cellResolution R
    (cellResolution R (cellResolution R P))) ⟶ postnikovDerivationTarget R D n hn :=
  cellAugmentation R (cellResolution R (cellResolution R (cellResolution R P))) ≫
    (cellAugmentation R (cellResolution R (cellResolution R P)) ≫
      (cellAugmentation R (cellResolution R P) ≫ postnikovCellLiftOverTarget R B D P n hn b h)) ≫
    postnikovPerturbedClass R D n hn

lemma postnikovCellFactorizationSource_projection :
    postnikovCellFactorizationSource R B D P n hn b h ≫
    SquareZero.projection (postnikov R D n) (postnikovShiftedLayerBimodule R D n hn 1) =
    postnikovCellFactorizationProjection R P ≫ (b ≫ postnikovMap R h n) := by
  rw [postnikovCellFactorizationSource, Category.assoc, Category.assoc,
    postnikovPerturbedClass_projection]
  exact postnikovCellFactorization_base R B D P n hn b h

lemma postnikovCellFactorizationTarget_projection :
    postnikovCellFactorizationTarget R B D P n hn b h ≫
    SquareZero.projection (postnikov R D n) (postnikovShiftedLayerBimodule R D n hn 1) =
    postnikovCellFactorizationProjection R P ≫ (b ≫ postnikovMap R h n) := by
  rw [postnikovCellFactorizationTarget, Category.assoc, Category.assoc,
    postnikovPerturbedClass_projection]
  have hb := congrArg (fun t =>
    cellAugmentation R (cellResolution R (cellResolution R (cellResolution R P))) ≫
    cellAugmentation R (cellResolution R (cellResolution R P)) ≫
    cellAugmentation R (cellResolution R P) ≫ t)
    (postnikovCellLiftOverTarget_projection R B D P n hn b h)
  simpa only [Category.assoc, postnikovCellFactorizationProjection] using hb

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
