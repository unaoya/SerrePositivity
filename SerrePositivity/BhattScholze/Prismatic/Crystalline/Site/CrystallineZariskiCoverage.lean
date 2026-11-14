module

public import SerrePositivity.BhattScholze.Prismatic.Crystalline.Site.CrystallineZariskiRefinement
public import Mathlib.CategoryTheory.Sites.Coverage
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Site.CrystallineSiteZariski

/-!
# affine 結晶サイトの主開 coverage

## 概要
有限主開被覆を coverage に組み、既存の生成 Grothendieck 位相と同一視する。

## 方針
局所化による細分を使って coverage の引き戻し公理を満たす。

## 規約
濃度上限は無限。反対圏の射をサイトの矢印とする。

## 使われ方
Berthelot III.4、Stacks 07HN–07JJ。構造前層の層条件を主開被覆で検査する。
-/

@[expose] public noncomputable section
universe u
open CategoryTheory
namespace SerrePositivity.BhattScholze.Prismatic
variable {p : ℕ} {k : Type u} [CommRing k] {J : Ideal k} {γ : DividedPowers J}
variable {R : Type u} [CommRing R] [Algebra (k ⧸ J) R] {κ : Cardinal.{u}}

/-- 有限主開局所化で与えられる被覆 presieve。 -/
def IsCrystallineCover (X : (CrysOver p γ R κ)ᵒᵖ) (S : Presieve X) : Prop :=
  ∃ (ι : Type u) (_ : Finite ι) (Y : ι → CrysOver p γ R κ)
    (f : ∀ i, X.unop ⟶ Y i), CrysOver.IsZariskiFamily Y f ∧
      S = Presieve.ofArrows (fun i => Opposite.op (Y i)) (fun i => (f i).op)

/-- 主開被覆の細分による結晶 Zariski coverage。 -/
def crystallineZariskiCoverage (hκ : Cardinal.aleph0 ≤ κ) :
    Coverage (CrysOver p γ R κ)ᵒᵖ where
  coverings X := { S | IsCrystallineCover X S }
  pullback := by
    rintro X Z h S ⟨ι, hι, Y, f, hf, rfl⟩
    obtain ⟨W, a, ha, b, hb⟩ := crysZariski_refinement hκ Y f hf h.unop
    refine ⟨Presieve.ofArrows (fun i => Opposite.op (W i)) (fun i => (a i).op),
      ⟨ι, hι, W, a, ha, rfl⟩, ?_⟩
    intro V v hv
    cases hv with
    | mk i =>
      refine ⟨Opposite.op (Y i), (b i).op, (f i).op, Presieve.ofArrows.mk i, ?_⟩
      apply Quiver.Hom.unop_inj
      exact hb i

/-- 主開 coverage が生成する位相は先に定めた結晶 Zariski 位相。 -/
theorem crystallineZariskiCoverage_toGrothendieck (hκ : Cardinal.aleph0 ≤ κ) :
    (crystallineZariskiCoverage (p := p) (γ := γ) (R := R) hκ).toGrothendieck =
      crystallineLargeZariskiTopology := by
  apply le_antisymm
  · rw [Coverage.toGrothendieck_eq_sInf]
    apply sInf_le
    rintro X S ⟨ι, hι, Y, f, hf, rfl⟩
    exact crystallineLargeZariskiTopology_cover Y f hf
  · apply crystallineLargeZariskiTopology_le
    intro ι hι X Y f hf
    exact Coverage.Saturate.of _ _ ⟨ι, hι, Y, f, hf, rfl⟩

end SerrePositivity.BhattScholze.Prismatic
