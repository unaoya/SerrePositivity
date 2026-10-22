module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovZeroPro
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovDesc

/-!
概要：零次数集中代数の群同型を実代数同型へ反映し、零切断への降下にも適用する。
方針：定数塔の実 pro 逆を回収し、元の商射の群同型で降下射を消去する。
規約：元の射の逆を供給。使われ方：元の一切断 roof の零切断の実分母同型。
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

lemma zeroAlgebra_map_isIso_of_groups {P T : Mon (Complex R)}
    [P.X.IsStrictlyGE 0] [P.X.IsStrictlyLE 0] [T.X.IsStrictlyGE 0] [T.X.IsStrictlyLE 0]
    (f : P ⟶ T) (hf : IsIso ((groups R 0).map f)) : IsIso f := by
  let a : LevelHom (Tower.constant P) (Tower.constant T) :=
    { app := fun _ => f, naturality := fun _ => by simp [Tower.constant] }
  have : ∀ i, IsIso ((a.map (groups R 0)).app i) := fun _ => hf
  have h := proIso_of_zeroAlgebra_groups R a
    (fun _ => by
      change P.X.IsStrictlyGE 0 ∧ P.X.IsStrictlyLE 0
      exact ⟨inferInstance, inferInstance⟩)
    (fun _ => by
      change T.X.IsStrictlyGE 0 ∧ T.X.IsStrictlyLE 0
      exact ⟨inferInstance, inferInstance⟩)
    (TowerDiagram.isProIso_of_levelwiseIso _)
  obtain ⟨k, hk, b, hb, bh⟩ := h 0
  exact ⟨⟨b, hb, bh⟩⟩

variable {P T : Mon (Complex R)} [P.X.IsStrictlyLE 0]
  [T.X.IsStrictlyGE 0] [T.X.IsStrictlyLE 0]

local instance zeroDescTarget_lowerBound : T.X.IsStrictlyGE (-(0 : ℤ)) := by
  simpa only [neg_zero] using (inferInstance : T.X.IsStrictlyGE 0)

local instance zeroDescSource_lowerBound : (postnikov R P 0).X.IsStrictlyGE 0 := by
  change ((postnikovComplex R 0).obj P).IsStrictlyGE 0
  simpa only [neg_zero] using postnikovComplex_lowerBound R P 0

local instance zeroDescSource_nonpositive : (postnikov R P 0).X.IsStrictlyLE 0 :=
  postnikovComplex_nonpositive R P 0

lemma postnikovDesc_zero_isIso_of_groups (f : P ⟶ T)
    (hf : IsIso ((groups R 0).map f)) : IsIso (postnikovDesc R 0 f) := by
  have := postnikovQuotient_groups_isIso R P 0 0 le_rfl
  have : IsIso ((groups R 0).map (postnikovQuotient R P 0) ≫
      (groups R 0).map (postnikovDesc R 0 f)) := by
    rw [← Functor.map_comp, postnikovQuotient_desc]
    exact hf
  have hd : IsIso ((groups R 0).map (postnikovDesc R 0 f)) :=
    IsIso.of_isIso_comp_left ((groups R 0).map (postnikovQuotient R P 0)) _
  exact zeroAlgebra_map_isIso_of_groups R _ hd

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
