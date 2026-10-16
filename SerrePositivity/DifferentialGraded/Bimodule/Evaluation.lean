module
public import SerrePositivity.DifferentialGraded.Bimodule.Category

/-! # 閉零bimodule圏の評価と全次数変換への復元 -/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.DifferentialGraded.BimoduleCategory
open CategoryTheory MonoidalCategory
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w)
  [DGCategory A B] [DGCategory A C] [Small.{u} B]

/-- 左対象を固定した、全次数自然な右加群への評価。 -/
def evaluation (c : C) : BimoduleCategory A B C ⥤ ModuleCategory A B where
  obj M := ForgetEnrichment.of (Complex A) ((underlying A B C M).rightAt c)
  map a := a.val c

@[ext]
lemma hom_ext {M N : BimoduleCategory A B C} {a b : M ⟶ N}
    (h : ∀ c, (evaluation A B C c).map a = (evaluation A B C c).map b) : a = b := by
  apply Subtype.ext
  funext c
  exact h c

@[simp]
lemma homEquiv_app {M N : BimoduleCategory A B C} (a : M ⟶ N) (c : C) :
    (homEquiv A B C M N a).app c =
      ForgetEnrichment.homTo (Complex A) ((evaluation A B C c).map a) := rfl

lemma homEquiv_comp_app {M N P : BimoduleCategory A B C} (a : M ⟶ N) (b : N ⟶ P)
    (c : C) :
    (homEquiv A B C M P (a ≫ b)).app c =
    (λ_ (𝟙_ (Complex A))).inv ≫
      ((homEquiv A B C M N a).app c ⊗ₘ (homEquiv A B C N P b).app c) ≫
      eComp (Complex A) ((underlying A B C M).rightAt c)
        ((underlying A B C N).rightAt c) ((underlying A B C P).rightAt c) := by
  change ForgetEnrichment.homTo (Complex A) (a.val c ≫ b.val c) =
    (λ_ (𝟙_ (Complex A))).inv ≫
      (ForgetEnrichment.homTo (Complex A) (a.val c) ⊗ₘ
        ForgetEnrichment.homTo (Complex A) (b.val c)) ≫ _
  exact (ForgetEnrichment.homTo_comp (Complex A) (a.val c) (b.val c)).trans
    (Category.assoc _ _ _)

end SerrePositivity.DifferentialGraded.BimoduleCategory
