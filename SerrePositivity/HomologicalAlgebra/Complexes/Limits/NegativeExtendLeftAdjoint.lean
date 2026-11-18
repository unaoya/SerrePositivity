module

public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.NormalizedChainsHom
public import Mathlib.CategoryTheory.Adjunction.Limits

/-!
# 負次数延長の実左随伴性

概要：元の非負鎖の零延長は smart 切断で表現される右随伴を持つ。
方針：実 Hom 同値とその始域自然性から随伴を構成する。
規約：元の extendFunctor と加群の宇宙を固定する。
使われ方：正規化単体の latching 余極限保存。
-/

@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.ComplexLimits
open _root_.CategoryTheory
variable (A : Type u) [CommRing A]

lemma nonpositiveExtend_isLeftAdjoint :
    ((ComplexShape.embeddingUpIntLE 0).extendFunctor (ModuleCat.{u} A)).IsLeftAdjoint :=
  (Adjunction.adjunctionOfEquivRight
    (F := (ComplexShape.embeddingUpIntLE 0).extendFunctor (ModuleCat.{u} A))
    (fun L H => _root_.SerrePositivity.EInfinity.ComplexLimits.extendTruncationHomEquiv L H)
    (fun _ _ H f g => _root_.SerrePositivity.EInfinity.ComplexLimits.extendTruncationHomEquiv_precomp H f g)).isLeftAdjoint

lemma negativeExtend_isLeftAdjoint :
    (ComplexShape.embeddingDownNat.extendFunctor (ModuleCat.{u} A)).IsLeftAdjoint := by
  rw [_root_.SerrePositivity.ComplexLimits.embeddingDownNat_eq_upIntLE_zero]
  exact _root_.SerrePositivity.ComplexLimits.nonpositiveExtend_isLeftAdjoint A

end SerrePositivity.ComplexLimits
