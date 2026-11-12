module

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.OrderNerveContraction

/-!
# 部分順序集合の nerve と頂点で指定する部分対象の同型

概要：部分順序を継承する部分集合の nerve を、全頂点が部分集合に属する部分単体集合と同定する。
方針：各単体の対象写像を部分型へ制限し、射は順序から作る。
規約：Moss arXiv:1506.04887v2 Proposition 2.19 の horn の面の順序集合への補助。
使われ方：部分単体集合の anodyne 性を、実際の nerve の包含へ移す。

対応節は Kerodon 3.3（Tag 00XF）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
namespace SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor
open CategoryTheory Limits MonoidalCategory

/--
概要：部分順序を継承する部分集合からの包含の単調写像。
方針：部分型の値を取る。
規約：性質の下方閉性は要求しない。
使われ方：部分集合の nerve の実際の包含。
-/
def orderSubtypeInclusion {P : Type u} [PartialOrder P] (S : P → Prop) : Subtype S →o P where
  toFun := Subtype.val
  monotone' _ _ h := h

/--
概要：部分順序集合の nerve と、全頂点で指定した部分単体集合との自然な同型。
方針：各頂点に性質の証明を付ける写像と、その証明を忘れる写像を使う。
規約：薄い圏の関手の等式は対象写像で確認する。
使われ方：horn の面の部分順序集合の包含。
-/
def orderNerveSubcomplexIso {P : Type u} [PartialOrder P] (S : P → Prop) :
    nerve (Subtype S) ≅ (orderNerveSubcomplex S : SSet.{u}) where
  hom :=
    { app d := ↾fun s =>
        ⟨(nerveMap (orderSubtypeInclusion S).monotone.functor).app d s,
          fun i => (s.obj i).property⟩
      naturality := by intros; rfl }
  inv :=
    { app _ := ↾fun s =>
        { obj i := ⟨s.val.obj i, s.property i⟩
          map f := homOfLE (leOfHom (s.val.map f))
          map_id _ := Subsingleton.elim _ _
          map_comp _ _ := Subsingleton.elim _ _ }
      naturality := by
        intros
        apply ConcreteCategory.hom_ext
        intro s
        apply nerve.ext_of_isThin
        rfl }
  hom_inv_id := by
    apply NatTrans.ext
    funext d
    apply ConcreteCategory.hom_ext
    intro s
    apply nerve.ext_of_isThin
    rfl
  inv_hom_id := by
    apply NatTrans.ext
    funext d
    apply ConcreteCategory.hom_ext
    intro s
    apply Subtype.ext
    apply nerve.ext_of_isThin
    rfl

/--
概要：部分順序集合の nerve の包含は、部分単体集合への同型とその包含の合成である。
方針：写像の各単体での定義を比較する。
規約：同型の向きは部分順序集合の nerve から部分対象へ向く。
使われ方：anodyne 性を包含の合成へ移す。
-/
theorem orderNerveSubcomplexIso_inclusion {P : Type u} [PartialOrder P] (S : P → Prop) :
    (orderNerveSubcomplexIso S).hom ≫ (orderNerveSubcomplex S).ι =
      nerveMap (orderSubtypeInclusion S).monotone.functor := rfl

/--
概要：上側を経由する相対収縮を持つ部分順序集合の nerve の包含は anodyne である。
方針：頂点で指定する部分対象への同型と、証明済みの収縮の補題を合成する。
規約：強い pairing を指定しない通常の anodyne 性。
使われ方：安全な面の nerve の包含への適用。
-/
theorem orderSubtypeNerve_anodyne {P : Type u} [PartialOrder P]
    (S : P → Prop) (p : P) (hp : S p) (g : P →o P)
    (hg : ∀ x, S x → S (g x)) (hId : ∀ x, x ≤ g x) (hP : ∀ x, p ≤ g x) :
    SSet.anodyneExtensions (nerveMap (orderSubtypeInclusion S).monotone.functor) := by
  rw [← orderNerveSubcomplexIso_inclusion]
  exact SSet.anodyneExtensions.comp_mem _ _ (SSet.anodyneExtensions.of_isIso _)
    (orderNerveSubcomplex_anodyne S p hp g hg hId hP)

end SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor
