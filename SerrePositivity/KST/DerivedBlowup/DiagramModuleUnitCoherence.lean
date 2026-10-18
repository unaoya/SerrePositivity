module

public import SerrePositivity.KST.DerivedBlowup.DiagramModuleTransitionUnit
public import SerrePositivity.KST.DerivedBlowup.DiagramModuleCoefficientCategory

/-!
概要：KST §3.1 の図式係数圏の指定単位矢の恒等・三重整合性。
方針：包含上の Hom 合成を展開し、係数射の単位保存とモノイドの単位律を使う。
規約：全有限重なりに対応する一般の前順序係数図式について示す。
使われ方：指定の加群比較の単位と三重比較の計算。
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

/-- 概要：恒等包含の指定単位矢は係数圏の恒等射。
方針：単位の二つの定義を照合する。
規約：KST §3.1。使われ方：図式加群比較の恒等条件。 -/
theorem diagramModuleTransitionUnit_id (i : J) :
    diagramModuleTransitionUnit F (le_refl i) = diagramModuleId F i := rfl

/-- 概要：二つの包含の指定単位矢の合成は直接包含の指定単位矢。
方針：包含 Hom の合成公式、係数射の単位保存、左単位律を使う。
規約：KST §3.1、閉零射の合成の unitor を明示する。
使われ方：加群作用に対する canonical な三重整合性。 -/
theorem diagramModuleTransitionUnit_comp {i j k : J} (h : i ≤ j) (g : j ≤ k) :
    (λ_ (𝟙_ (Complex R))).inv ≫
      (diagramModuleTransitionUnit F h ⊗ₘ diagramModuleTransitionUnit F g) ≫
        diagramModuleComp F i j k = diagramModuleTransitionUnit F (h.trans g) := by
  unfold diagramModuleTransitionUnit
  rw [← tensorHom_comp_tensorHom_assoc, diagramModuleComp_on_le]
  rw [← Category.assoc (MonObj.one ⊗ₘ MonObj.one), tensorHom_comp_tensorHom]
  simp only [Category.comp_id, IsMonHom.one_hom]
  rw [tensorHom_def', Category.assoc, MonObj.one_mul_assoc, leftUnitor_naturality_assoc,
    Iso.inv_hom_id_assoc]

/-- 概要：前順序係数図式から係数 dg 圏の閉零射圏への指定単位関手。
方針：包含を単位矢に送り、証明した恒等律・合成律で束ねる。
規約：KST §3.1、加群の貼り合わせ条件ではなく係数圏内の関手。
使われ方：指定の加群遷移の全ての包含鎖に沿う整合性。 -/
def diagramModuleUnitFunctor : J ⥤ ClosedCategory R (DiagramModuleCoefficientObject F) where
  obj i := ForgetEnrichment.of (Complex R) ⟨i⟩
  map f := ForgetEnrichment.homOf (Complex R) (diagramModuleTransitionUnit F (leOfHom f))
  map_id i := diagramModuleTransitionUnit_id F i
  map_comp f g := (diagramModuleTransitionUnit_comp F (leOfHom f) (leOfHom g)).symm

end SerrePositivity.KST.DerivedBlowup
