module

public import SerrePositivity.AlgebraicGeometry.AffineOpenVCoverRefinement
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-!
概要：G1と同じ有限アフィン被覆の余積で、相対fppfの平坦性と全射性を保つ。
方針：平坦性と局所有限表示性を元の各開被覆の脚で確認する。
規約：新しい模型や平坦化を選ばず、同じ元の射への細分を保持する。
使われ方：中間の非アフィンなブローアップ上の相対fppfの係数比較の入口。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
set_option backward.isDefEq.respectTransparency false

/-- 同じ有限アフィン開被覆の余積で、相対の平坦全射と局所有限表示性を保つ。 -/
theorem exists_affine_flatSurjective_refinement {W B : Scheme.{u}}
    (f : W ⟶ B) [CompactSpace W] [B.IsSeparated]
    [Flat f] [Surjective f] [LocallyOfFinitePresentation f] :
    ∃ (A : Scheme.{u}) (_ : IsAffine A) (m : A ⟶ W),
      Flat (m ≫ f) ∧ Surjective (m ≫ f) ∧
        LocallyOfFinitePresentation (m ≫ f) ∧ IsAffineHom (m ≫ f) := by
  classical
  let 𝒰 := W.affineCover.finiteSubcover
  have (i : 𝒰.I₀) : IsAffine (𝒰.X i) := inferInstanceAs (IsAffine (Spec _))
  let A : Scheme.{u} := ∐ 𝒰.X
  letI : IsAffine A := by dsimp [A]; infer_instance
  let m : A ⟶ W := Sigma.desc 𝒰.f
  haveI : Flat (m ≫ f) := by
    apply IsZariskiLocalAtSource.of_openCover (P := @Flat) (sigmaOpenCover 𝒰.X)
    intro i
    change Flat (Sigma.ι 𝒰.X i ≫ m ≫ f)
    rw [← Category.assoc, Sigma.ι_comp_desc]
    infer_instance
  haveI : LocallyOfFinitePresentation (m ≫ f) := by
    apply IsZariskiLocalAtSource.of_openCover (P := @LocallyOfFinitePresentation)
      (sigmaOpenCover 𝒰.X)
    intro i
    change LocallyOfFinitePresentation (Sigma.ι 𝒰.X i ≫ m ≫ f)
    rw [← Category.assoc, Sigma.ι_comp_desc]
    infer_instance
  haveI : Surjective m := inferInstanceAs (Surjective (Sigma.desc 𝒰.f))
  haveI : IsAffineHom ((m ≫ f) ≫ terminal.from B) := by
    rw [terminal.comp_from]
    infer_instance
  haveI : IsAffineHom (m ≫ f) := IsAffineHom.of_comp (m ≫ f) (terminal.from B)
  exact ⟨A, inferInstance, m, inferInstance, inferInstance, inferInstance, inferInstance⟩

end SerrePositivity.AlgebraicGeometry
