module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraProRoof

/-!
概要：元の pro 逆の実 roof に、厳密な左持ち上げと右の実乗法的経路を保持する。
方針：元の MappingPath の切断と経路を、元の第一射の eventual な逆へ合成する。
規約：局所化後の等式から経路を選ばない。使われ方：元の class 逆の底変更。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
open ProExcision SurjectiveRoof
variable (R : Type u) [CommRing R] {X Y Z : Tower (Mon (Complex R))}

/-- 左三角形は実持ち上げで厳密、右三角形は元の乗法的経路で保持する。 -/
def HasNativeRoofProInverse (f : LevelHom X Y) : Prop :=
  ∀ i, ∃ m, ∃ hi : i ≤ m, ∃ r : SurjectiveRoof R (Y.obj m) (X.obj i),
    ∃ a : X.obj m ⟶ r.apex,
      a ≫ r.denominator = f.app m ∧ a ≫ r.numerator = X.transition hi ∧
        Nonempty (Path.Witness R (r.numerator ≫ f.app i) (r.denominator ≫ Y.transition hi))

lemma hasNativeRoofProInverse_of_factor (a : LevelHom X Z) (b : LevelHom Z Y)
    (ha : IsProIso a) (hb : ∀ i, QuasiIso (b.app i).hom) :
    HasNativeRoofProInverse R (a.comp b) := by
  intro i
  obtain ⟨m, hi, c, hc, ch⟩ := ha i
  let r := (ofQuasiIsoInverse R (b.app m) (hb m)).postcompose R c
  refine ⟨m, hi, r, a.app m ≫ MappingPath.section_ R (b.app m), ?_, ?_, ?_⟩
  · change (a.app m ≫ MappingPath.section_ R (b.app m)) ≫
      MappingPath.target R (b.app m) = a.app m ≫ b.app m
    rw [Category.assoc, MappingPath.section_target]
  · change (a.app m ≫ MappingPath.section_ R (b.app m)) ≫
      (MappingPath.projection R (b.app m) ≫ c) = X.transition hi
    rw [Category.assoc, ← Category.assoc (MappingPath.section_ R (b.app m)),
      MappingPath.section_projection, Category.id_comp]
    exact hc
  · let w := (MappingPath.pathWitness R (b.app m)).postcomp (Y.transition hi)
    have he : (MappingPath.projection R (b.app m) ≫ c) ≫ (a.app i ≫ b.app i) =
        (MappingPath.projection R (b.app m) ≫ b.app m) ≫ Y.transition hi := by
      calc
        _ = MappingPath.projection R (b.app m) ≫ ((c ≫ a.app i) ≫ b.app i) := by
          simp only [Category.assoc]
        _ = MappingPath.projection R (b.app m) ≫ (Z.transition hi ≫ b.app i) := by rw [ch]
        _ = MappingPath.projection R (b.app m) ≫ (b.app m ≫ Y.transition hi) := by
          rw [b.naturality hi]
        _ = _ := (Category.assoc _ _ _).symm
    exact ⟨{ hom := w.hom, source_eq := w.source_eq.trans he.symm, target_eq := w.target_eq }⟩

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
