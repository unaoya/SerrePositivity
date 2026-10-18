module

public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.CategoryTheory.Preadditive.Injective.LiftingProperties

/-!
概要：生成対象の部分対象からの射の injective 因子化で injectivity を判定する。
方針：中間 injective 対象を使って生成対象へ延長し、生成単射の右持ち上げ判定を使う。
規約：Grothendieck アーベル圏の実際の生成対象。
使われ方：Stacks 19.12.5・19.12.6、TT §3・§8、Toën §3.2 の非有界複体の各項 injectivity。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe w v u
open CategoryTheory Limits ZeroObject
namespace SerrePositivity.KST.DerivedGeometry
variable {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{w} C]

/--
概要：生成対象の全部分対象からの射が injective 対象を経由すれば終域は injective。
方針：各因子を生成対象へ延長して、生成単射の右持ち上げと injectivity の同値を使う。
規約：因子化を injectivity そのものの未証明フィールドとして定義しない。
使われ方：Stacks 19.12.5・19.12.6、TT §3・§8、Toën §3.2 の非有界 injective 模型の判定。
-/
lemma injective_of_generator_injective_factors (G : C) (hG : IsSeparator G) (I : C)
    (h : ∀ (S : Subobject G) (f : (S : C) ⟶ I),
      ∃ (J : C) (_ : Injective J) (a : (S : C) ⟶ J) (b : J ⟶ I), a ≫ b = f) : Injective I := by
  apply (injective_iff_rlp_monomorphisms_zero I).mpr
  rw [← IsGrothendieckAbelian.generatingMonomorphisms_rlp hG]
  rintro _ _ _ ⟨S⟩
  constructor
  intro f g sq
  obtain ⟨J, hJ, a, b, hab⟩ := h S f
  have : Injective J := hJ
  exact ⟨⟨{ l := Injective.factorThru a S.arrow ≫ b
            fac_left := by rw [← Category.assoc, Injective.comp_factorThru, hab]
            fac_right := by apply Subsingleton.elim }⟩⟩

end SerrePositivity.KST.DerivedGeometry
