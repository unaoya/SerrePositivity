module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraQuasiIsoLocalization

/-!
概要：下に有界な元の代数の塔から有限切断への射を、通常局所化で pro 同型判定する。
方針：上の有限切断商を準同型とし、有限範囲の零層に対する実 pro 逆と合成する。
規約：元の代数の塔・商射・遷移を保持。使われ方：bounded-below な切断比較。
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
variable (R : Type u) [CommRing R]

lemma postnikovQuotient_quasiIso (B : Mon (Complex R)) [B.X.IsStrictlyLE 0]
    (a : ℤ) (hB : B.X.IsGE (-a)) : QuasiIso (postnikovQuotient R B a).hom :=
  (CochainComplex.quasiIso_πTruncGE_iff B.X (-a)).2 hB

variable (A : Tower (NonpositiveAlgebra R))

def postnikovQuotientLevelHom (n : ℤ) :
    LevelHom (A.map (nonpositiveInclusion R)) (A.map (postnikovFunctor R n)) :=
  TowerDiagram.mapNat A (postnikovQuotientNatTrans R n)

lemma postnikovQuotientLevelHom_transition (a b : ℤ) (hab : b ≤ a) :
    (postnikovQuotientLevelHom R A a).comp (postnikovTransitionLevelHom R A a b hab) =
      postnikovQuotientLevelHom R A b := by
  apply ProSpectrum.levelHom_ext
  intro i
  exact postnikovQuotient_transition R (A.obj i).obj a b hab

variable {C : Type v} [Category.{w} C] (L : Mon (Complex R) ⥤ C)

lemma postnikovQuotientLevelHom_isProIso_of_bounded (hL : InvertsQuasiIsos R L)
    (b : ℤ) (hb : 0 ≤ b) (a : ℤ) (hab : b ≤ a)
    (hB : ∀ i, (A.obj i).obj.X.IsGE (-a))
    (hA : ∀ j : ℤ, b < j → j ≤ a →
      IsProZero ((A.map (nonpositiveInclusion R)).map (groups R j))) :
    IsProIso ((postnikovQuotientLevelHom R A b).map L) := by
  have : ∀ i, IsIso (((postnikovQuotientLevelHom R A a).map L).app i) :=
    fun i => hL _ (postnikovQuotient_quasiIso R (A.obj i).obj a (hB i))
  have hu := TowerDiagram.isProIso_of_levelwiseIso ((postnikovQuotientLevelHom R A a).map L)
  have ht := postnikovTransitionLevelHom_isProIso_finite R A L hL b hb a hab hA
  have hc := hu.comp ht
  rw [← TowerDiagram.levelHom_map_comp, postnikovQuotientLevelHom_transition] at hc
  exact hc

lemma postnikovQuotientQuasiIsoLocalization_isProIso_of_bounded
    (b : ℤ) (hb : 0 ≤ b) (a : ℤ) (hab : b ≤ a)
    (hB : ∀ i, (A.obj i).obj.X.IsGE (-a))
    (hA : ∀ j : ℤ, b < j → j ≤ a →
      IsProZero ((A.map (nonpositiveInclusion R)).map (groups R j))) :
    IsProIso ((postnikovQuotientLevelHom R A b).map (quasiIsoLocalization R)) :=
  postnikovQuotientLevelHom_isProIso_of_bounded R A (quasiIsoLocalization R)
    (quasiIsoLocalization_inverts R) b hb a hab hB hA

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
