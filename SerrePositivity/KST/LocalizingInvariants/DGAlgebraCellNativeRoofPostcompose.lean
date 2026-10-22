module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraCellNativeProRoof

/-!
概要：実三角形付き roof の逆を、実代数の pro 同型との後合成に沿って保持する。
方針：元の eventual 逆と pullback を使い、左は一回の cell 後で厳密に持ち上げる。
規約：元の右経路を射影と元の射に沿って運ぶ。使われ方：元の一切断射の実逆。
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
variable (R : Type u) [CommRing R] {X Y Z : Tower (Mon (Complex R))}
  (f : LevelHom X Y) (g : LevelHom Y Z)

/-- 実代数の右側の逆を使い、元の右経路と左持ち上げを保持する。 -/
def CellNativeInverseRoof.postcompose {i m k : ℕ} (hi : i ≤ m) (hk : m ≤ k)
    (c : CellNativeInverseRoof R f i m hi) (v : Z.obj k ⟶ Y.obj m)
    (hv : g.app k ≫ v = Y.transition hk) (vh : v ≫ g.app m = Z.transition hk) :
    CellNativeInverseRoof R (f.comp g) i k (hi.trans hk) := by
  let t := SurjectiveRoof.comp R (SurjectiveRoof.ofHom R v) c.roof
  let u := cellResolutionMapLift R (X.transition hk)
    (iteratedCellAugmentation R (X.obj m) c.sourceDepth)
    (iteratedCellAugmentation_surjective R (X.obj m) c.sourceDepth)
    (iteratedCellAugmentation_quasiIso R (X.obj m) c.sourceDepth)
  have hu : u ≫ iteratedCellAugmentation R (X.obj m) c.sourceDepth =
      cellAugmentation R (X.obj k) ≫ X.transition hk := cellResolutionMapLift_projection R _ _ _ _
  let l := u ≫ c.sourceLift
  let z := cellAugmentation R (X.obj k) ≫ (f.app k ≫ g.app k)
  have hl : z ≫ v = l ≫ c.roof.denominator := by
    change (cellAugmentation R (X.obj k) ≫ (f.app k ≫ g.app k)) ≫ v =
      (u ≫ c.sourceLift) ≫ c.roof.denominator
    rw [Category.assoc, Category.assoc, hv, Category.assoc u, c.source_denominator,
      ← Category.assoc u, hu, Category.assoc, f.naturality hk]
  let q := MonoidPullback.lift v c.roof.denominator z l hl
  refine ⟨t, 1, q, ?_, ?_, ?_⟩
  · change q ≫ (MonoidPullback.fst v c.roof.denominator ≫ 𝟙 _) = _
    rw [← Category.assoc, MonoidPullback.lift_fst, Category.comp_id]
    simp only [z, iteratedCellAugmentation, iteratedCellResolution, Category.comp_id]
    rfl
  · change q ≫ (MonoidPullback.snd v c.roof.denominator ≫ c.roof.numerator) = _
    rw [← Category.assoc, MonoidPullback.lift_snd]
    change (u ≫ c.sourceLift) ≫ c.roof.numerator = _
    rw [Category.assoc, c.source_numerator, ← Category.assoc, hu, Category.assoc,
      X.transition_comp]
    simp only [iteratedCellAugmentation, iteratedCellResolution, Category.comp_id]
  · let s := MonoidPullback.snd v c.roof.denominator
    let w := (c.rightPath.precomp s).postcomp (g.app i)
    have hpb : s ≫ c.roof.denominator = t.denominator ≫ v := by
      change MonoidPullback.snd v c.roof.denominator ≫ c.roof.denominator =
        (MonoidPullback.fst v c.roof.denominator ≫ 𝟙 (Z.obj k)) ≫ v
      rw [Category.comp_id]
      exact (MonoidPullback.condition v c.roof.denominator).symm
    have he : (s ≫ (c.roof.denominator ≫ Y.transition hi)) ≫ g.app i =
        t.denominator ≫ Z.transition (hi.trans hk) := by
      calc
        _ = (s ≫ c.roof.denominator) ≫ (Y.transition hi ≫ g.app i) := by
          simp only [Category.assoc]
        _ = (t.denominator ≫ v) ≫ (g.app m ≫ Z.transition hi) := by
          rw [hpb, g.naturality hi]
        _ = t.denominator ≫ ((v ≫ g.app m) ≫ Z.transition hi) := by
          simp only [Category.assoc]
        _ = _ := by rw [vh, Z.transition_comp]
    refine { hom := w.hom, source_eq := ?_, target_eq := w.target_eq.trans he }
    change w.hom ≫ Path.source R (Z.obj i) =
      (s ≫ c.roof.numerator) ≫ (f.app i ≫ g.app i)
    exact w.source_eq.trans (Category.assoc _ _ _)


lemma HasCellNativeRoofProInverse.postcompose (hf : HasCellNativeRoofProInverse R f)
    (hg : IsProIso g) : HasCellNativeRoofProInverse R (f.comp g) := by
  intro i
  obtain ⟨m, hi, ⟨c⟩⟩ := hf i
  obtain ⟨k, hk, v, hv, vh⟩ := hg m
  exact ⟨k, hi.trans hk, ⟨c.postcompose R f g hi hk v hv vh⟩⟩

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
