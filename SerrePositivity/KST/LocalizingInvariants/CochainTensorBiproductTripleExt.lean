module

public import SerrePositivity.KST.LocalizingInvariants.TensorBiproductExt

/-!
概要：三重 tensor の左二因子の直和成分による射の一致判定。
方針：実内部 Hom への curry によって二因子の成分判定へ戻す。
規約：平坦性を仮定しない。使われ方：dg 平方零拡大の結合則の八成分計算。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants

variable {R : Type u} [CommRing R] {A B P T : Complex R}

lemma cochainBiprodTensorPairLeft_hom_ext
    {f g : ((A ⊞ B) ⊗ (A ⊞ B)) ⊗ P ⟶ T}
    (hll : ((biprod.inl ⊗ₘ biprod.inl) ▷ P) ≫ f =
      ((biprod.inl ⊗ₘ biprod.inl) ▷ P) ≫ g)
    (hlr : ((biprod.inl ⊗ₘ biprod.inr) ▷ P) ≫ f =
      ((biprod.inl ⊗ₘ biprod.inr) ▷ P) ≫ g)
    (hrl : ((biprod.inr ⊗ₘ biprod.inl) ▷ P) ≫ f =
      ((biprod.inr ⊗ₘ biprod.inl) ▷ P) ≫ g)
    (hrr : ((biprod.inr ⊗ₘ biprod.inr) ▷ P) ≫ f =
      ((biprod.inr ⊗ₘ biprod.inr) ▷ P) ≫ g) : f = g := by
  apply (tensorRightHomEquiv P ((A ⊞ B) ⊗ (A ⊞ B)) T).injective
  change curryRight f = curryRight g
  apply biprodTensor_hom_ext
  · simpa only [← tensorHom_id, curryRight_naturality_source] using congrArg curryRight hll
  · simpa only [← tensorHom_id, curryRight_naturality_source] using congrArg curryRight hlr
  · simpa only [← tensorHom_id, curryRight_naturality_source] using congrArg curryRight hrl
  · simpa only [← tensorHom_id, curryRight_naturality_source] using congrArg curryRight hrr

end SerrePositivity.KST.LocalizingInvariants
