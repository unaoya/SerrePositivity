module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.AdjunctNaturality
public import Mathlib.CategoryTheory.Adjunction.FullyFaithful

/-!
概要：双圏随伴が各 Hom 圏の後合成に誘導する通常の随伴。
方針：adjunct 全単射と二変数自然性を通常の随伴へ移す。
規約：任意の双圏で述べる。使われ方：B2 の余単位の可逆性を h Fun 全体で得る。

対応節は Kerodon 6.2（Tag 02EH）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory Bicategory
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories

/-- 概要：双圏の随伴は各パラメータの Hom 圏で後合成の随伴を与える。
方針：標準 adjunct 全単射と前後合成の自然性を使う。
規約：通常の圏の随伴へ移す。使われ方：充満忠実な後合成からの余単位の可逆性。 -/
def bicategoryPostcompAdjunction {B : Type u} [Bicategory.{w, v} B]
    {a b : B} {f : a ⟶ b} {g : b ⟶ a} (adj : Bicategory.Adjunction f g) (c : B) :
    Bicategory.postcomp c f ⊣ Bicategory.postcomp c g :=
  CategoryTheory.Adjunction.mkOfHomEquiv {
    homEquiv := fun _ _ => adj.homEquiv₂
    homEquiv_naturality_left_symm := by
      intro U' U V α β
      change (adj.homEquiv₂ (g := U') (h := V)).symm (α ≫ β) =
        α ▷ f ≫ (adj.homEquiv₂ (g := U) (h := V)).symm β
      apply adj.homEquiv₂.injective
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.bicategoryAdjunct_naturality_left, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    homEquiv_naturality_right := fun α β => _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.bicategoryAdjunct_naturality_right adj α β }

/-- 概要：後合成随伴の恒等一胞体での余単位は元の余単位を単位子で輸送したもの。
方針：adjunct 逆写像の式を展開して coherence を揃える。
規約：元の余単位の代表は変更しない。使われ方：通常の随伴の結果を双圏へ戻す。 -/
lemma bicategoryPostcompAdjunction_counit_identity {B : Type u} [Bicategory.{w, v} B]
    {a b : B} {f : a ⟶ b} {g : b ⟶ a} (adj : Bicategory.Adjunction f g) :
    ((λ_ g).inv ▷ f) ≫ (bicategoryPostcompAdjunction adj b).counit.app (𝟙 b) = adj.counit := by
  change ((λ_ g).inv ▷ f) ≫
    (adj.homEquiv₂ (g := (𝟙 b) ≫ g) (h := 𝟙 b)).symm (𝟙 _) = adj.counit
  dsimp [Bicategory.Adjunction.homEquiv₂]
  bicategory

/-- 概要：右随伴の後合成が充満忠実なら双圏随伴の余単位は可逆。
方針：各 Hom 圏の通常の随伴に充満忠実な右随伴の定理を適用する。
規約：右側の対象をパラメータとする一つの Hom 圏の充満忠実性で足りる。
使われ方：反射的包含の余単位の可逆性。 -/
lemma bicategory_counit_isIso_of_postcomp_fullyFaithful
    {B : Type u} [Bicategory.{w, v} B] {a b : B} {f : a ⟶ b} {g : b ⟶ a}
    (adj : Bicategory.Adjunction f g) (h : (Bicategory.postcomp b g).FullyFaithful) :
    IsIso adj.counit := by
  letI := h.full
  letI := h.faithful
  let e := bicategoryPostcompAdjunction adj b
  haveI : IsIso e.counit := inferInstance
  rw [← bicategoryPostcompAdjunction_counit_identity adj]
  infer_instance

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories
