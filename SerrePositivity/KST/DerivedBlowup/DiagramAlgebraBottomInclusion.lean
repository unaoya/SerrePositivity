module

public import SerrePositivity.KST.DerivedBlowup.DiagramAlgebraWithBottom
public import SerrePositivity.KST.DerivedBlowup.DiagramModuleCoefficientCategory

/-!
概要：KST §3.1 の補助始点つき係数圏への元の係数圏の包含。
方針：元の頂点間の Hom をそのまま同定し、単位・合成を保持する。
規約：元の係数 dg 圏と全図式加群の模型を保持する。
使われ方：補助頂点の representable の制限。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v

namespace SerrePositivity.KST.DerivedBlowup

open CategoryTheory CategoryTheory.MonoidalCategory
open DifferentialGraded

variable {R : Type u} [CommRing R] {J : Type v} [Preorder J] [DecidableLE J]
variable (F : J ⥤ Mon (Complex R))

/-- 概要：補助始点を加えても元の頂点間の Hom 複体は同じ。
方針：包含条件と目標代数がそれぞれ元のものに一致することを使う。
規約：KST §3.1。使われ方：係数圏の包含の Hom 写像。 -/
theorem diagramAlgebraWithBottom_hom (i j : J) :
    diagramModuleHom F i j =
      diagramModuleHom (diagramAlgebraWithBottom F) (i : WithBot J) (j : WithBot J) := by
  simp only [diagramModuleHom, WithBot.coe_le_coe]
  rfl

set_option maxHeartbeats 2000000 in
-- 元の頂点間の Hom の等式に沿う tensor と合成の移送を照合するために必要。
/-- 概要：元の係数圏から補助始点つき係数圏への指定 dg 包含。
方針：対象を元の頂点へ送り、Hom の標準同定で送る。
規約：KST §3.1。使われ方：共変 representable を元の図式へ制限する。 -/
def diagramAlgebraBottomInclusion :
    DGFunctor R (DiagramModuleCoefficientObject F)
      (DiagramModuleCoefficientObject (diagramAlgebraWithBottom F)) where
  obj x := ⟨(x.index : WithBot J)⟩
  map x y := eqToHom (diagramAlgebraWithBottom_hom F x.index y.index)
  map_id x := by
    change diagramModuleId F x.index ≫ eqToHom _ =
      diagramModuleId (diagramAlgebraWithBottom F) (x.index : WithBot J)
    simp only [diagramModuleId, diagramModuleHomInclusion, Category.assoc, eqToHom_trans]
  map_comp x y z := by
    change diagramModuleComp F x.index y.index z.index ≫ eqToHom _ =
      (eqToHom _ ⊗ₘ eqToHom _) ≫ diagramModuleComp (diagramAlgebraWithBottom F)
        (x.index : WithBot J) (y.index : WithBot J) (z.index : WithBot J)
    by_cases h : x.index ≤ y.index
    · by_cases g : y.index ≤ z.index
      · simp only [diagramModuleComp, WithBot.coe_le_coe, dite_eq_left h, dite_eq_left g,
          diagramModuleHomInclusion, Category.assoc, tensorHom_comp_tensorHom_assoc,
          eqToHom_trans]
        simp only [← Category.assoc, eqToHom_trans]
        rfl
      · simp only [diagramModuleComp, WithBot.coe_le_coe, dite_eq_left h, dite_eq_right g,
          Limits.zero_comp, Limits.comp_zero]
    · simp only [diagramModuleComp, WithBot.coe_le_coe, dite_eq_right h,
        Limits.zero_comp, Limits.comp_zero]

end SerrePositivity.KST.DerivedBlowup
