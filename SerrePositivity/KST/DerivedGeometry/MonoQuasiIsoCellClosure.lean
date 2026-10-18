module

public import SerrePositivity.KST.DerivedGeometry.MonoQuasiIsoStability
public import Mathlib.CategoryTheory.MorphismProperty.TransfiniteComposition

/-!
概要：非有界単射準同型は coproduct・押し出し・超限合成・retract の cell 構成で保たれる。
方針：完全な余極限での保存を射の性質にまとめ、Mathlib の超限合成の一般定理を使う。
規約：Grothendieck アーベル圏の宇宙に合わせる。
使われ方：Stacks 19.12.4・19.12.6、TT §3・§8、Toën §3.2 の非有界 K-injective 分解。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe w v u
open CategoryTheory Limits MorphismProperty
namespace SerrePositivity.KST.DerivedGeometry
variable {C : Type u} [Category.{v} C] [Abelian C]

/-- 概要：単射準同型は同型不変。
方針：二つの射の性質の共通部分を使う。
規約：非有界。使われ方：Stacks 19.12.6、TT §3 の cell の比較。 -/
instance monicQuasiIsomorphisms_respectsIso : (monicQuasiIsomorphisms (C := C)).RespectsIso := by
  change (monomorphisms _ ⊓ HomologicalComplex.quasiIso C (.up ℤ)).RespectsIso
  infer_instance

/-- 概要：単射準同型は恒等と合成で閉じる。
方針：二つの既存の乗法的な射の性質を組み合わせる。
規約：非有界。使われ方：Stacks 19.12.6、TT §3 の超限合成。 -/
instance monicQuasiIsomorphisms_multiplicative : (monicQuasiIsomorphisms (C := C)).IsMultiplicative := by
  change (monomorphisms _ ⊓ HomologicalComplex.quasiIso C (.up ℤ)).IsMultiplicative
  infer_instance

/-- 概要：単射準同型は retract で保たれる。
方針：各性質の retract での安定性を使う。
規約：非有界。使われ方：Stacks 19.12.6、TT §3 の small object factorization。 -/
instance monicQuasiIsomorphisms_retracts : (monicQuasiIsomorphisms (C := C)).IsStableUnderRetracts := by
  change (monomorphisms _ ⊓ HomologicalComplex.quasiIso C (.up ℤ)).IsStableUnderRetracts
  infer_instance

/--
概要：完全な余極限は単射準同型を保つ。
方針：単射と準同型のそれぞれの余極限保存を同じ余錐に適用する。
規約：複体の上下限は不要。
使われ方：Stacks Theorem 19.12.6、TT §3 の極限順序数。
-/
instance monicQuasiIsomorphisms_exactColimits
    (J : Type*) [Category* J] [HasColimitsOfShape J C] [HasExactColimitsOfShape J C] :
    (monicQuasiIsomorphisms (C := C)).IsStableUnderColimitsOfShape J where
  condition F G c₁ c₂ h₁ h₂ f hf φ hφ :=
    ⟨IsStableUnderColimitsOfShape.condition (W := monomorphisms (CochainComplex C ℤ))
      F G c₁ c₂ h₁ h₂ f (fun j => (hf j).1) φ hφ,
     IsStableUnderColimitsOfShape.condition (W := HomologicalComplex.quasiIso C (.up ℤ))
      F G c₁ c₂ h₁ h₂ f (fun j => (hf j).2) φ hφ⟩

variable [IsGrothendieckAbelian.{w} C]

/-- 概要：単射準同型は小さい filtered colimit で保たれる。
方針：Grothendieck 性の AB5 を使う。
規約：同じ宇宙。使われ方：Stacks 19.12.6、TT §3 の超限極限。 -/
instance monicQuasiIsomorphisms_filteredColimits :
    IsStableUnderFilteredColimits.{w, w} (monicQuasiIsomorphisms (C := C)) where
  isStableUnderColimitsOfShape J := inferInstance

/-- 概要：単射準同型は小さい coproduct で保たれる。
方針：Grothendieck 性の AB4 を使う。
規約：同じ宇宙。使われ方：Stacks 19.12.4、TT §3 の cell 付加。 -/
instance monicQuasiIsomorphisms_coproducts : IsStableUnderCoproducts.{w} (monicQuasiIsomorphisms (C := C)) where
  isStableUnderCoproductsOfShape J := inferInstance

/-- 概要：単射準同型は小さい超限合成で保たれる。
方針：乗法性と filtered colimit での保存に Mathlib の一般定理を適用する。
規約：同じ宇宙。使われ方：Stacks 19.12.6、TT §3・§8 の非有界分解。 -/
instance monicQuasiIsomorphisms_transfinite :
    (monicQuasiIsomorphisms (C := C)).IsStableUnderTransfiniteComposition.{w} := inferInstance

end SerrePositivity.KST.DerivedGeometry
