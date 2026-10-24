module

public import SerrePositivity.InfinityCategories.F1B.KanExtension.LeftCommaUniversalDiagram
public import SerrePositivity.InfinityCategories.F1B.KanExtension.LeftCommaHom

/-!
概要：底で選んだ普遍図式の変換を元の添字へ制限すると恒等の類になる。
方針：厳密化が保つ指定変換の類を恒等矢印の包含で制限する。
規約：単なる両端の一致でなく、実際の変換の h Fun の類を計算する。
使われ方：普遍図式への前合成を標準局所 Kan 条件と比較する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F1B

/-- 概要：底での普遍変換を恒等矢印の包含へ制限した自己変換。
方針：厳密化後の変換を前合成し、両端を δ に同一視する。
規約：raw なホモトピーは厳密化後の prism の制限を保つ。
使われ方：標準の恒等変換との類の比較。 -/
def kanLeftCommaUniversalIdentityHomotopy {K C : SSet.{u}} [Quasicategory C]
    (δ : K ⟶ C) : SSet.Homotopy δ δ := by
  let T := functorHomotopyPrecomp (kanLeftCommaUniversalStrictification δ).2.transformation
    (kanLeftCommaInclusion δ)
  refine { h := T.h, h₀ := ?_, h₁ := ?_, rel := T.rel }
  · rw [T.h₀, ← Category.assoc, kanLeftCommaInclusion_source, Category.id_comp]
    rfl
  · rw [T.h₁, ← Category.assoc, kanLeftCommaInclusion_projection, Category.comp_id]
    rfl

/-- 概要：普遍変換を元の添字へ制限した自己変換の類は恒等射。
方針：選んだ厳密化の類の保存を前合成し、元の comma 変換の定値性を使う。
規約：厳密化後の変換自体が定値であることは仮定しない。
使われ方：局所条件を元の F の恒等指定変換の相対 Kan 条件へ戻す。 -/
lemma kanLeftCommaUniversalIdentityHomotopy_hom {K C : SSet.{u}} [Quasicategory C]
    (δ : K ⟶ C) :
    SSet.Truncated.HomotopyCategory.homMk
        (functorEdgeOfSimplicialHomotopy (kanLeftCommaUniversalIdentityHomotopy δ)) =
      𝟙 (HomotopyCategory.mk (functorVertex δ)) := by
  let r := (kanLeftCommaUniversalStrictification δ).2
  let T := functorHomotopyPrecomp r.transformation (kanLeftCommaInclusion δ)
  let B := functorHomotopyPrecomp (kanLeftCommaUniversalHomotopy δ) (kanLeftCommaInclusion δ)
  have hh : SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy T) =
      SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy B) := by
    rw [functorHomotopyPrecomp_hom, functorHomotopyPrecomp_hom, r.transformation_hom_eq]
  have h₀ : kanLeftCommaInclusion δ ≫ (kanLeftCommaSource δ ≫ δ) = δ := by
    rw [← Category.assoc, kanLeftCommaInclusion_source, Category.id_comp]
  have h₁ : kanLeftCommaInclusion δ ≫ (kanLeftCommaProjection δ ≫ 𝟙 C) = δ := by
    rw [← Category.assoc, kanLeftCommaInclusion_projection, Category.comp_id]
  have hT := kanHomotopyHom_transport T (kanLeftCommaUniversalIdentityHomotopy δ) h₀ h₁ rfl
  have hB := kanHomotopyHom_transport B (functorHomotopyRefl δ) h₀ h₁
    (kanLeftCommaHomotopy_inclusion_h δ)
  rw [hh] at hT
  exact hT.symm.trans (hB.trans (functorHomotopyRefl_hom δ))

end SerrePositivity.InfinityCategories.F1B
