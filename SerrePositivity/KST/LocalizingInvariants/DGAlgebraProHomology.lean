module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraHomology
public import SerrePositivity.KST.LocalizingInvariants.ProGroupIsoCriterion

/-!
概要：元の dg 代数の塔の整数ホモロジー群による pro 連結度・pro 同値を定義する。
方針：元の H⁻ʲ 関手を実レベル射へ適用し、既存の核・像の eventual 条件を使う。
規約：一般 pro ∞ 圏での連結度・同値とは同一視しない。使われ方：実因子分解の群判定。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory HomologicalComplex
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
open ProExcision
variable (R : Type u) [CommRing R]

lemma groups_map_isIso_of_quasiIsoAt {B C : Mon (Complex R)} (f : B ⟶ C) (j : ℤ)
    (hf : QuasiIsoAt f.hom (-j)) : IsIso ((groups R j).map f) := by
  have : IsIso (homologyMap f.hom (-j)) := (quasiIsoAt_iff_isIso_homologyMap _ _).1 hf
  change IsIso (AddCommGrpCat.toCommGrp.map
    ((forget₂ (ModuleCat R) AddCommGrpCat).map (homologyMap f.hom (-j))))
  infer_instance

lemma groups_subsingleton_of_homology_zero (B : Mon (Complex R)) (j : ℤ)
    (h : CategoryTheory.Limits.IsZero (B.X.homology (-j))) : Subsingleton ((groups R j).obj B) := by
  have := (ModuleCat.isZero_iff_subsingleton).1 h
  change Subsingleton (Multiplicative (B.X.homology (-j)))
  infer_instance

def IsPiProConnected {X Y : Tower (Mon (Complex R))} (f : LevelHom X Y) (n : ℤ) : Prop :=
  (∀ j : ℤ, j < n → ProGroup.IsEventuallyKernelTrivial (f.map (groups R j))) ∧
    ∀ j : ℤ, j ≤ n → ProGroup.IsEventuallyImageSurjective (f.map (groups R j))

def IsPiProEquivalence {X Y : Tower (Mon (Complex R))} (f : LevelHom X Y) : Prop :=
  ProExcision.IsProEquivalence (fun j : ℤ => groups R j) f

lemma IsPiProConnected.groupMap_isProIso {X Y : Tower (Mon (Complex R))} {f : LevelHom X Y}
    {n j : ℤ} (h : IsPiProConnected R f n) (hj : j < n) : IsProIso (f.map (groups R j)) :=
  ProGroup.proIso_of_kernel_image (h.1 j hj) (h.2 j hj.le)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
