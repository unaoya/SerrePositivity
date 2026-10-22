module

public import SerrePositivity.EInfinity.ComplexLimits.ExtendTruncationHom

/-!
# 延長と smart 切断の Hom 同値の元の始域射との整合

概要：逆向きは元の延長射と包含の合成であり、始域の全鎖射に自然。
方針：元の延長関手の合成保存と Hom 同値の両逆を使う。
規約：元の射と包含を保持する。
使われ方：標準単体の全作用素と Dold–Kan Hom の接続。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.ComplexLimits
open CategoryTheory HomologicalComplex CochainComplex
open SerrePositivity.DifferentialGraded
variable {A : Type u} [CommRing A]

lemma extendTruncationHomEquiv_symm_apply (L : ChainComplex (ModuleCat.{u} A) ℕ)
    (H : Complex A) (f : L ⟶ H.truncLE' (ComplexShape.embeddingUpIntLE 0)) :
    (extendTruncationHomEquiv L H).symm f =
      extendMap f (ComplexShape.embeddingUpIntLE 0) ≫
        (H.truncLEIso (ComplexShape.embeddingUpIntLE 0)).inv ≫ H.ιTruncLE 0 := rfl

lemma extendTruncationHomEquiv_symm_comp
    {L L' : ChainComplex (ModuleCat.{u} A) ℕ} (H : Complex A) (g : L' ⟶ L)
    (f : L ⟶ H.truncLE' (ComplexShape.embeddingUpIntLE 0)) :
    (extendTruncationHomEquiv L' H).symm (g ≫ f) =
      extendMap g (ComplexShape.embeddingUpIntLE 0) ≫ (extendTruncationHomEquiv L H).symm f := by
  simp only [extendTruncationHomEquiv_symm_apply, extendMap_comp, Category.assoc]

lemma extendTruncationHomEquiv_precomp
    {L L' : ChainComplex (ModuleCat.{u} A) ℕ} (H : Complex A) (g : L' ⟶ L)
    (f : L.extend (ComplexShape.embeddingUpIntLE 0) ⟶ H) :
    extendTruncationHomEquiv L' H (extendMap g (ComplexShape.embeddingUpIntLE 0) ≫ f) =
      g ≫ extendTruncationHomEquiv L H f := by
  apply (extendTruncationHomEquiv L' H).symm.injective
  rw [Equiv.symm_apply_apply, extendTruncationHomEquiv_symm_comp, Equiv.symm_apply_apply]

end SerrePositivity.EInfinity.ComplexLimits
