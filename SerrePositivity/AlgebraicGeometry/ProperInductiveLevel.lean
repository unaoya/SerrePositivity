module

public import SerrePositivity.AlgebraicGeometry.ProperFlatteningNoetherian

/-!
概要：BS17 Definition 2.5 の固有全射の帰納的レベルの実際の証人。
方針：nilimmersion・proper fppf・閉中心上の一段低いレベルを再帰的に保持する。
規約：存在はこの定義からは主張しない。閉中心は実際のイデアル層で表す。
使われ方：G3 の Lemma 2.6 の次元帰納と G4 の Čech 判定。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory Limits
universe u

/-- BS17 Definition 2.5 の帰納的レベル。nilimmersion は全射な有限表示閉埋め込みで表す。 -/
def ProperInductiveLevel : ℕ → {X Y : Scheme.{u}} → (X ⟶ Y) → Prop
  | 0, X, Y, f =>
    ∃ (X' Y' : Scheme.{u}) (i : Y' ⟶ Y) (q : X' ⟶ Y') (a : X' ⟶ X),
      IsClosedImmersion i ∧ Surjective i ∧ LocallyOfFinitePresentation i ∧
      IsProper q ∧ Flat q ∧ Surjective q ∧ LocallyOfFinitePresentation q ∧
      a ≫ f = q ≫ i
  | n + 1, X, Y, f =>
    ∃ (X' X₀ Y₀ : Scheme.{u}) (i : Y₀ ⟶ Y) (r : X₀ ⟶ Y₀)
      (q : X' ⟶ X₀) (a : X' ⟶ X) (J : Y₀.IdealSheafData),
      IsClosedImmersion i ∧ Surjective i ∧ LocallyOfFinitePresentation i ∧
      IsProper r ∧ Surjective r ∧ LocallyOfFinitePresentation r ∧
      LocallyOfFinitePresentation J.subschemeι ∧ IsIso (r ∣_ centerComplement J) ∧
      ProperInductiveLevel n (pullback.snd r J.subschemeι) ∧
      IsProper q ∧ Flat q ∧ Surjective q ∧ LocallyOfFinitePresentation q ∧
      a ≫ f = q ≫ r ≫ i

namespace ProperInductiveLevel

/-- proper fppf 射は、nilimmersion に恒等射を選ぶことでレベル0。 -/
theorem of_proper_fppf {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsProper f] [Flat f] [Surjective f] [LocallyOfFinitePresentation f] :
    ProperInductiveLevel 0 f := by
  exact ⟨X, Y, 𝟙 Y, f, 𝟙 X, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, by simp⟩

/-- 帰納的レベルは、実際の細分の射を合成することで精密化から消去できる。 -/
theorem of_refinement {X Y Z : Scheme.{u}} {n : ℕ} {f : X ⟶ Y}
    (hf : ProperInductiveLevel n f) (a : X ⟶ Z) (g : Z ⟶ Y) (ha : a ≫ g = f) :
    ProperInductiveLevel n g := by
  cases n with
  | zero =>
    obtain ⟨X', Y', i, q, b, hi, his, hif, hq, hqf, hqs, hqfp, hb⟩ := hf
    exact ⟨X', Y', i, q, b ≫ a, hi, his, hif, hq, hqf, hqs, hqfp, by
      rw [Category.assoc, ha, hb]⟩
  | succ n =>
    obtain ⟨X', X₀, Y₀, i, r, q, b, J, hi, his, hif, hr, hrs, hrf, hJ, hIso,
      hn, hq, hqf, hqs, hqfp, hb⟩ := hf
    exact ⟨X', X₀, Y₀, i, r, q, b ≫ a, J, hi, his, hif, hr, hrs, hrf, hJ, hIso,
      hn, hq, hqf, hqs, hqfp, by rw [Category.assoc, ha, hb]⟩

end ProperInductiveLevel
end SerrePositivity.AlgebraicGeometry
