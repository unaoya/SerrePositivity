module

public import SerrePositivity.KST.LocalizingInvariants.ProMonoidReflection
public import SerrePositivity.KST.LocalizingInvariants.ProZeroComplexReflection
public import SerrePositivity.KST.LocalizingInvariants.ProLevelwiseInverse
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovFunctor

/-!
概要：元の π₀ 群の pro 同型から、元の零 Postnikov 代数の実 pro 同型を構成する。
方針：群の逆を線形・零集中複体・単位と積を保つ逆へ戻し、元の商射の正方形を使う。
規約：環構造を追加入力しない。使われ方：一般の矢印塔の有限 Postnikov 比較の零段。
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
variable (R : Type u) [CommRing R]

lemma proIso_of_zeroAlgebra_groups {X Y : Tower (Mon (Complex R))} (f : LevelHom X Y)
    (hX : ∀ i, (zeroComplexProperty R) (X.obj i).X)
    (hY : ∀ i, (zeroComplexProperty R) (Y.obj i).X)
    (hf : IsProIso (f.map (groups R 0))) : IsProIso f :=
  TowerDiagram.proIso_of_monoid_forget f
    (TowerDiagram.proIso_of_zeroComplex_groups R (f.map (Mon.forget (Complex R))) hX hY hf)

variable {A B : Tower (NonpositiveAlgebra R)} (f : LevelHom A B)

lemma postnikovZeroMap_groups_proIso
    (hf : IsProIso ((f.map (nonpositiveInclusion R)).map (groups R 0))) :
    IsProIso ((f.map (postnikovFunctor R 0)).map (groups R 0)) := by
  let a := TowerDiagram.mapNat A (postnikovQuotientNatTrans R 0)
  let b := TowerDiagram.mapNat B (postnikovQuotientNatTrans R 0)
  have : ∀ i, IsIso ((a.map (groups R 0)).app i) :=
    fun i => postnikovQuotient_groups_isIso R (A.obj i).obj 0 0 le_rfl
  have : ∀ i, IsIso ((b.map (groups R 0)).app i) :=
    fun i => postnikovQuotient_groups_isIso R (B.obj i).obj 0 0 le_rfl
  apply TowerDiagram.proIso_of_square ((f.map (nonpositiveInclusion R)).map (groups R 0))
    ((f.map (postnikovFunctor R 0)).map (groups R 0)) (a.map (groups R 0))
    (b.map (groups R 0)) ?_ hf
  apply ProSpectrum.levelHom_ext
  intro i
  change (groups R 0).map (f.app i).hom ≫
      (groups R 0).map (postnikovQuotient R (B.obj i).obj 0) =
    (groups R 0).map (postnikovQuotient R (A.obj i).obj 0) ≫
      (groups R 0).map (postnikovMap R (f.app i).hom 0)
  rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
  exact congrArg (groups R 0).map (postnikovQuotient_naturality R (f.app i).hom 0).symm

/-- 元の π₀ の pro 比較は、単位・積を保つ零切断の実代数 pro 逆を与える。 -/
lemma postnikovZeroMap_isProIso
    (hf : IsProIso ((f.map (nonpositiveInclusion R)).map (groups R 0))) :
    IsProIso (f.map (postnikovFunctor R 0)) := by
  apply proIso_of_zeroAlgebra_groups R (f.map (postnikovFunctor R 0))
    (fun i => ?_) (fun i => ?_) (postnikovZeroMap_groups_proIso R f hf)
  · constructor
    · change ((postnikovComplex R 0).obj (A.obj i).obj).IsStrictlyGE 0
      simpa only [neg_zero] using postnikovComplex_lowerBound R (A.obj i).obj 0
    · exact postnikovComplex_nonpositive R (A.obj i).obj 0
  · constructor
    · change ((postnikovComplex R 0).obj (B.obj i).obj).IsStrictlyGE 0
      simpa only [neg_zero] using postnikovComplex_lowerBound R (B.obj i).obj 0
    · exact postnikovComplex_nonpositive R (B.obj i).obj 0

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
