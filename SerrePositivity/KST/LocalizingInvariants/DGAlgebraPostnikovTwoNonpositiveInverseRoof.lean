module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraBoundedRightInverseRoof
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraNativeRightRoofRetarget
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovTwoDiagonalLeftReflection
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraNonpositiveInverseRoofOfLeftPath

/-!
概要：元の三次数の pro 同型から、元の二切断射の実両三角形付き非正次数逆を構成する。
方針：対角の実右逆の段を先に選び、その段の元の右逆の左欠損を反映し厳密化する。
規約：対角の逆や左経路を追加入力にしない。使われ方：高次有限 Postnikov 段の底。
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
  (h₀ : IsProIso ((f.map (nonpositiveInclusion R)).map (groups R 0)))
  (h₁ : IsProIso ((f.map (nonpositiveInclusion R)).map (groups R 1)))
  (h₂ : IsProIso ((f.map (nonpositiveInclusion R)).map (groups R 2)))

include h₀ h₁ h₂

lemma exists_postnikovTwoDiagonalRightInverseRoof (i : ℕ) :
    ∃ m, ∃ hi : i ≤ m, Nonempty (NativeRightInverseRoof R
      ((postnikovTwoNonpositiveDiagonal R f).map (nonpositiveInclusion R)) i m hi) := by
  apply exists_boundedNativeRightInverseRoof R (postnikovTwoNonpositiveDiagonal R f)
  · intro j
    change (postnikov R (A.obj j).obj 2).X.IsGE (-2)
    have := postnikov_lowerBound R (A.obj j).obj 2
    infer_instance
  · intro j
    have := postnikovTwoDiagonalTarget_lowerBound R f j
    infer_instance
  · exact postnikovTwoNonpositiveDiagonal_groups_proIso R f h₀ h₁ h₂ 0 (by omega) (by omega)
  · exact postnikovTwoNonpositiveDiagonal_groups_proIso R f h₀ h₁ h₂ 1 (by omega) (by omega)
  · exact postnikovTwoNonpositiveDiagonal_groups_proIso R f h₀ h₁ h₂ 2 (by omega) (by omega)

lemma postnikovTwoMap_exists_nonpositiveInverseRoof (i : ℕ) :
    ∃ k, ∃ hi : i ≤ k,
      Nonempty (NonpositiveInverseRoof R (f.map (postnikovFunctor R 2)) i k hi) := by
  obtain ⟨m, him, ⟨q⟩⟩ := exists_postnikovTwoDiagonalRightInverseRoof R f h₀ h₁ h₂ i
  obtain ⟨k, hmk, ⟨c⟩⟩ := exists_postnikovTwoNativeRightInverseRoof R f h₀ h₁ h₂ m
  have : ((A.map (postnikovFunctor R 2)).obj k).X.IsStrictlyLE 0 :=
    postnikov_nonpositive R (A.obj k).obj 2
  have : ((B.map (postnikovFunctor R 2)).obj k).X.IsStrictlyLE 0 :=
    postnikov_nonpositive R (B.obj k).obj 2
  let c' := c.retarget R him
  let T := c.nonpositiveSource R
  let p := cellAugmentation R T ≫ c.sourceProjection R
  let a : cellResolution R T ⟶ c'.roof.apex := cellAugmentation R T ≫ c.sourceLift R
  have hp : ∀ n : ℤ, Function.Surjective (p.hom.f n) := fun n =>
    (c.sourceProjection_surjective R n).comp (cellAugmentation_surjective R T n)
  have hq : QuasiIso p.hom := quasiIso_comp _ _
    (hφ := cellAugmentation_quasiIso R T) (hφ' := c.sourceProjection_quasiIso R)
  have hd : a ≫ c'.roof.denominator = p ≫ postnikovMap R (f.app k).hom 2 := by
    change (cellAugmentation R T ≫ c.sourceLift R) ≫ c.roof.denominator = _
    rw [Category.assoc, c.sourceLift_denominator R, ← Category.assoc]
    rfl
  let w := postnikovTwoDiagonalLeftReflection R f q c
  let w' : Path.Witness R (a ≫ c'.roof.numerator)
      (p ≫ postnikovMap R (A.transition (him.trans hmk)).hom 2) :=
    ⟨w.hom,
      w.source_eq.trans (by
        change cellAugmentation R T ≫ ((c.sourceLift R ≫ c.roof.numerator) ≫
          postnikovMap R (A.transition him).hom 2) =
          (cellAugmentation R T ≫ c.sourceLift R) ≫
            (c.roof.numerator ≫ postnikovMap R (A.transition him).hom 2)
        simp only [Category.assoc]),
      w.target_eq.trans (Category.assoc _ _ _).symm⟩
  exact ⟨k, him.trans hmk, ⟨c'.nonpositiveOfLeftPath R p hp hq a hd w'⟩⟩

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
