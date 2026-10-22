module
public import SerrePositivity.InfinityCategories.Derived.FunctorIsoSandwichTail
/-!
概要：中間の消去比較を変えた一般合成子の同じ値を計算する。
方針：指定された同型の値と関手 ∞ 圏の二胞体を保持する。
規約：古い比較との一致を先取りしない。使われ方：一般 cell 合成の単位 coherence。
-/
@[expose] public section
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory SSet
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
lemma functorIsoSandwichCompositor_middle_change {X A B Y C Z : SSet.{u}}
    (s : X ⟶ A) (h : B ⟶ Y) (i : Y ⟶ B) (t : C ⟶ Z)
    (e e' : FunctorIso (h ≫ i) (𝟙 B))
    (F : X ⟶ Y) (G : Y ⟶ Z) (M : A ⟶ B) (N : B ⟶ C) (T : A ⟶ C)
    (a : FunctorIso F (s ≫ M ≫ h)) (b : FunctorIso G (i ≫ N ≫ t))
    (k : FunctorIso (M ≫ N) T) :
    functorIsoSandwichCompositor s h i t e' F G M N T a b k =
      functorIsoSandwichCompositor s h i t e F G M N T a b k ≪≫
        ((k.postcomp t).precomp s).symm ≪≫
        FunctorIso.precomp
          (FunctorIso.postcomp (f := 𝟙 B) (g := 𝟙 B) (e.symm ≪≫ e') (N ≫ t))
          (s ≫ M) ≪≫
        (k.postcomp t).precomp s := by
  simp only [functorIsoSandwichCompositor_tail, functorIsoSandwichTail,
    F2.functorIso_precomp_trans, F2.functorIso_postcomp_trans,
    F2.functorIso_precomp_precomp,
    F2.functorIso_precomp_symm, F2.functorIso_postcomp_symm, Iso.trans_assoc,
    Iso.self_symm_id_assoc]
end
end SerrePositivity.InfinityCategories
