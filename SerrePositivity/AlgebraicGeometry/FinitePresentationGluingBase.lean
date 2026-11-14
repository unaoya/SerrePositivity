module

public import Mathlib.AlgebraicGeometry.Gluing
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation

/-!
概要：有限表示の模型のチャートを貼り合わせ、同じ基底への実際の射と局所性を保つ。
方針：glue data の multicoequalizer の構造射を取り、元のチャート上で性質を判定する。
規約：模型の gluing datum の存在はこのファイルの結論に含めない。
使われ方：G2 の一般の有限表示対象の模型の貼り合わせ。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory Limits
universe u
variable (D : Scheme.GlueData.{u}) {S : Scheme.{u}}
  (p : ∀ i, D.U i ⟶ S)
  (hp : ∀ i j, D.f i j ≫ p i = D.t i j ≫ D.f j i ≫ p j)

/-- チャートの基底への射を、同じ基底への実際の構造射へ貼り合わせる。 -/
def glueDataToBase : D.glued ⟶ S :=
  Multicoequalizer.desc D.toGlueData.diagram S p (by
    rintro ⟨i, j⟩
    change D.f i j ≫ p i = (D.t i j ≫ D.f j i) ≫ p j
    simpa only [Category.assoc] using hp i j)

/-- 貼り合わせた構造射は、元の各チャートで指定した射に一致する。 -/
@[reassoc] theorem glueDataToBase_ι (i : D.J) :
    D.ι i ≫ glueDataToBase D p hp = p i :=
  Multicoequalizer.π_desc _ _ _ _ _

/-- 基底への局所有限表示性は、貼り合わせる前の各チャートで判定できる。 -/
theorem locallyOfFinitePresentation_glueDataToBase
    (h : ∀ i, LocallyOfFinitePresentation (p i)) :
    LocallyOfFinitePresentation (glueDataToBase D p hp) := by
  refine IsZariskiLocalAtSource.of_openCover (P := @LocallyOfFinitePresentation)
    D.openCover (fun i ↦ ?_)
  change LocallyOfFinitePresentation (D.ι i ≫ glueDataToBase D p hp)
  rw [glueDataToBase_ι]
  exact h i

/-- 有限個の affine Noether チャートを貼り合わせた模型は Noether。 -/
theorem isNoetherian_glueData_of_finite_affine [Finite D.J]
    [∀ i, IsAffine (D.U i)] (h : ∀ i, IsNoetherianRing Γ(D.U i, ⊤)) :
    IsNoetherian D.glued := by
  letI : Finite D.openCover.I₀ := inferInstanceAs (Finite D.J)
  letI (i : D.openCover.I₀) : IsAffine (D.openCover.X i) := inferInstanceAs (IsAffine (D.U i))
  exact (isNoetherian_iff_of_finite_affine_openCover (𝒰 := D.openCover)).mpr h

/-- 有限個の affine Noether チャートの局所有限表示射を貼り合わせると qcqs な局所有限表示射。 -/
theorem finitePresentation_glueDataToBase_of_noetherian_charts [Finite D.J]
    [∀ i, IsAffine (D.U i)] (hN : ∀ i, IsNoetherianRing Γ(D.U i, ⊤))
    (hfp : ∀ i, LocallyOfFinitePresentation (p i)) :
    LocallyOfFinitePresentation (glueDataToBase D p hp) ∧
      QuasiCompact (glueDataToBase D p hp) ∧ QuasiSeparated (glueDataToBase D p hp) := by
  letI : IsNoetherian D.glued := isNoetherian_glueData_of_finite_affine D hN
  exact ⟨locallyOfFinitePresentation_glueDataToBase D p hp hfp, inferInstance, inferInstance⟩

end SerrePositivity.AlgebraicGeometry
