module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.RelativeFunctorRestrictedEndpoint

/-!
概要：同じ相対端点評価を、元の実延長と元の実終点の頂点で読む。
方針：恒等包含を持つ相対延長として既存の頂点公式を適用する。
規約：底・実射を保持。使われ方：全 prism 比較の成分と元の指定比較の照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.F2

/-- 元の全相対端点評価は、同じ実終点の相対頂点そのものを返す。 -/
lemma relativeFunctorRestrictedEndpoint_vertex {A C E F B : SSet.{u}}
    (p : E ⟶ B) (b : A ⟶ B) (j : C ⟶ A) (q : F ⟶ B) (a : C ⟶ F)
    (hj : j ≫ b = a ≫ q) (W : A ⟶ E) (hW : W ≫ p = b)
    (g : C ⟶ pullback p q) (hg : g ≫ pullback.snd p q = a)
    (hWj : j ≫ W = g ≫ pullback.fst p q) :
    (relativeFunctorRestrictedEndpoint p b j q a hj).app _ (relativeFunctorVertex p b W hW) =
      relativeFunctorVertex (pullback.snd p q) a g hg :=
  relativeFunctorExtensionEndpoint_vertex p b (𝟙 A) W
    (by rw [hW, Category.id_comp]) j q a hj W hW (Category.id_comp W) g hg hWj

end SerrePositivity.InfinityCategories.F2
