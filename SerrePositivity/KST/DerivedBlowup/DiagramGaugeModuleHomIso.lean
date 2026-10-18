module

public import SerrePositivity.KST.DerivedBlowup.DiagramGaugeFunctor
public import SerrePositivity.DifferentialGraded.Module.RestrictionEnriched
public import SerrePositivity.DifferentialGraded.Functor.Opposite

/-!
概要：KST v4 §3.1（pp.11–14）の捻りを表す gauge 制限は全次数 Hom を保つ。
方針：gauge の各 Hom 同型を消去し、制限後の豊穣自然性から元の自然性を復元する。
規約：原典と異なる図式加群模型での証明。H⁰ の同値だけで代用しない。
使われ方：実際の dg 捻りの全 Hom 写像の同型性。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v

namespace SerrePositivity.KST.DerivedBlowup

open CategoryTheory CategoryTheory.MonoidalCategory DifferentialGraded

variable {R : Type u} [CommRing R] {J : Type v} [Preorder J] [DecidableLE J]
variable (F : J ⥤ Mon (Complex R)) (s : DiagramHomGauge F)

/-- 概要：gauge 制限後のパラメータ付き豊穣自然変換を元の加群へ戻す。
方針：対象成分を保ち、各 Hom の可逆な重み付けを自然性から消去する。
規約：KST §3.1。使われ方：全 Hom 複体の逆写像の普遍性。 -/
def diagramGaugeModuleUnrestrictParam {K : Complex R}
    {M N : RightModule R (DiagramModuleCoefficientObject F)ᵒᵖ}
    (τ : ModuleParamTrans R (DiagramModuleCoefficientObject F)ᵒᵖ K
      (restrictModule R _ _ (diagramGaugeDGFunctor F s).op.op M)
      (restrictModule R _ _ (diagramGaugeDGFunctor F s).op.op N)) :
    ModuleParamTrans R (DiagramModuleCoefficientObject F)ᵒᵖ K M N where
  app x := τ.app x
  naturality x y := by
    let g : (x ⟶[Complex R] y) ⟶ (x ⟶[Complex R] y) :=
      (diagramGaugeDGFunctor F s).op.op.map x y
    let : IsIso g := diagramGaugeDGFunctor_map_isIso F s x.unop.unop y.unop.unop
    change (β_ K (x ⟶[Complex R] y)).hom ≫
      (M.map x y ⊗ₘ τ.app y) ≫ enrichedComposition _ _ _ =
        (τ.app x ⊗ₘ N.map x y) ≫ enrichedComposition _ _ _
    apply (cancel_epi (𝟙 K ⊗ₘ g)).mp
    rw [BraidedCategory.braiding_naturality_assoc]
    have ht := τ.naturality x y
    change (β_ K (x ⟶[Complex R] y)).hom ≫
      ((g ≫ M.map x y) ⊗ₘ τ.app y) ≫ enrichedComposition _ _ _ =
        (τ.app x ⊗ₘ (g ≫ N.map x y)) ≫ enrichedComposition _ _ _ at ht
    simpa only [tensorHom_comp_tensorHom_assoc, Category.id_comp, Category.comp_id]
      using ht

variable [Small.{u} (DiagramModuleCoefficientObject F)]

/-- 概要：gauge 制限後の全 Hom end から元の Hom end への chain map。
方針：全次数自然性の復元を Hom end の普遍性に適用する。
規約：KST §3.1。使われ方：指定制限 Hom 写像の逆。 -/
def diagramGaugeModuleHomInv (M N : RightModule R (DiagramModuleCoefficientObject F)ᵒᵖ) :
    moduleHom R (DiagramModuleCoefficientObject F)ᵒᵖ
      (restrictModule R _ _ (diagramGaugeDGFunctor F s).op.op M)
      (restrictModule R _ _ (diagramGaugeDGFunctor F s).op.op N) ⟶
      moduleHom R (DiagramModuleCoefficientObject F)ᵒᵖ M N :=
  (moduleHomEquiv R _ _ M N).symm
    (diagramGaugeModuleUnrestrictParam F s ((moduleHomEquiv R _ _ _ _) (𝟙 _)))

/-- 概要：全 Hom の逆写像は各対象成分を変えない。
方針：Hom end の普遍性の評価公式を使う。
規約：KST §3.1。使われ方：指定逆の両側逆条件。 -/
@[reassoc]
theorem diagramGaugeModuleHomInv_π
    (M N : RightModule R (DiagramModuleCoefficientObject F)ᵒᵖ)
    (d : (DiagramModuleCoefficientObject F)ᵒᵖ) :
    diagramGaugeModuleHomInv F s M N ≫ moduleHomπ R _ M N d =
      moduleHomπ R _
        (restrictModule R _ _ (diagramGaugeDGFunctor F s).op.op M)
        (restrictModule R _ _ (diagramGaugeDGFunctor F s).op.op N) d := by
  rw [diagramGaugeModuleHomInv, moduleHomEquiv_symm_π]
  exact Category.id_comp _

/-- 概要：gauge 制限の指定全 Hom 写像は複体同型。
方針：対象成分を保つ逆写像を構成し、両側逆を全評価で確認する。
規約：KST §3.1。使われ方：整数捻りの dg 完全忠実性。 -/
def diagramGaugeModuleHomIso (M N : RightModule R (DiagramModuleCoefficientObject F)ᵒᵖ) :
    moduleHom R (DiagramModuleCoefficientObject F)ᵒᵖ M N ≅
      moduleHom R (DiagramModuleCoefficientObject F)ᵒᵖ
        (restrictModule R _ _ (diagramGaugeDGFunctor F s).op.op M)
        (restrictModule R _ _ (diagramGaugeDGFunctor F s).op.op N) where
  hom := moduleRestrictionHom R _ _ (diagramGaugeDGFunctor F s).op.op M N
  inv := diagramGaugeModuleHomInv F s M N
  hom_inv_id := by
    apply moduleHom_ext
    intro d
    rw [Category.assoc, diagramGaugeModuleHomInv_π, moduleRestrictionHom_π]
    exact (Category.id_comp _).symm
  inv_hom_id := by
    apply moduleHom_ext
    intro d
    rw [Category.assoc, moduleRestrictionHom_π, diagramGaugeModuleHomInv_π]
    exact (Category.id_comp _).symm

end SerrePositivity.KST.DerivedBlowup
