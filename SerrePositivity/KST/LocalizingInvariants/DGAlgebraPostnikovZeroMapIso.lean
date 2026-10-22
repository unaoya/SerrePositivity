module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovStrictZeroSourceEquivalence
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovStrictZeroClassFactor

/-!
概要：元の零次数群の同型から元の零 Postnikov 代数の実同型を回収する。
方針：定数塔に実 pro 逆の反映を適用して、単位と積を保つ元の逆射を取り出す。
規約：源側の零切断には追加の群の仮定は不要。使われ方：層の作用を同じ底へ移す。
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

lemma postnikovZeroMap_isIso_of_groups {B C : NonpositiveAlgebra R} (f : B ⟶ C)
    (hf : IsIso ((groups R 0).map f.hom)) : IsIso (postnikovMap R f.hom 0) := by
  let a : LevelHom (Tower.constant B) (Tower.constant C) :=
    { app := fun _ => f, naturality := fun _ => by simp [Tower.constant] }
  have : ∀ i, IsIso (((a.map (nonpositiveInclusion R)).map (groups R 0)).app i) :=
    fun _ => hf
  have h := postnikovZeroMap_isProIso R a (TowerDiagram.isProIso_of_levelwiseIso _)
  obtain ⟨m, hm, b, hb, bh⟩ := h 0
  refine ⟨⟨b, ?_, ?_⟩⟩
  · change postnikovMap R f.hom 0 ≫ b = (postnikovFunctor R 0).map (𝟙 B) at hb
    exact hb.trans ((postnikovFunctor R 0).map_id B)
  · change b ≫ postnikovMap R f.hom 0 = (postnikovFunctor R 0).map (𝟙 C) at bh
    exact bh.trans ((postnikovFunctor R 0).map_id C)

variable {A B : Tower (NonpositiveAlgebra R)} (f : LevelHom A B) (n : ℤ) (hn : 0 ≤ n)

/-- 元の源の持ち上げの零切断は、各段で実代数の同型である。 -/
lemma postnikovStrictZeroBaseLift_zeroMap_isIso (i : ℕ) :
    IsIso (postnikovMap R ((postnikovStrictZeroBaseNonpositiveLift R f n hn).app i).hom 0) :=
  postnikovZeroMap_isIso_of_groups R _ (postnikovStrictZeroBaseLift_groups_zero_isIso R f n hn i)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
