module

public import Mathlib.CategoryTheory.Localization.LocalizerMorphism

/-!
# 相対関手の両側の弱同値比較から普通の局所化の同値を構成する

概要：Dwyer–Kan の相対圏比較の普通の局所化への効果を具体的に構成する。
方針：指定された両相対関手と自然な弱同値を局所化へ降ろす。
規約：これは普通の圏の局所化の比較であり、単体的局所化性は別に証明する。
使われ方：cofibrant 置換を保持した E2b の準備。
-/

@[expose] public section

noncomputable section

universe u v

namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.RelativeLocalization

open CategoryTheory

variable {C : Type u} [Category C] {D : Type v} [Category D]
  {W : MorphismProperty C} {V : MorphismProperty D}
  (F : LocalizerMorphism W V) (G : LocalizerMorphism V W)
  (a : F.functor ⋙ G.functor ⟶ 𝟭 C) (b : G.functor ⋙ F.functor ⟶ 𝟭 D)
  (ha : ∀ X, W (a.app X)) (hb : ∀ Y, V (b.app Y))

/-- 概要：指定した相対関手と弱同値比較から局所化の同値を構成（Dwyer–Kan）。
方針：両比較の全成分を反転し、局所化の充満忠実性で両逆を復元する。
規約：順逆関手は元の F・G の同じ局所化。
使われ方：cofibrant 置換と包含の普通の局所化における比較。 -/
def equivalence : W.Localization ≌ V.Localization := by
  have : IsIso (Functor.whiskerRight a W.Q) := by
    rw [NatTrans.isIso_iff_isIso_app]
    exact fun X => Localization.inverts W.Q W _ (ha X)
  have : IsIso (Functor.whiskerRight b V.Q) := by
    rw [NatTrans.isIso_iff_isIso_app]
    exact fun Y => Localization.inverts V.Q V _ (hb Y)
  refine Localization.equivalence W.Q W V.Q V (F.functor ⋙ V.Q)
    (F.localizedFunctor W.Q V.Q) (G.functor ⋙ W.Q) (G.localizedFunctor V.Q W.Q) ?_ ?_
  · exact Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (CatCommSq.iso G.functor V.Q W.Q _).symm ≪≫
      (Functor.associator _ _ _).symm ≪≫
      asIso (Functor.whiskerRight a W.Q) ≪≫ Functor.leftUnitor _
  · exact Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (CatCommSq.iso F.functor W.Q V.Q _).symm ≪≫
      (Functor.associator _ _ _).symm ≪≫
      asIso (Functor.whiskerRight b V.Q) ≪≫ Functor.leftUnitor _

/-- 概要：同値の順関手は元の相対関手 F の局所化そのもの（Dwyer–Kan）。
方針：局所化の同値の構成の順関手を評価する。
規約：別の同値関手を選ばない。
使われ方：元の包含からの比較射の追跡。 -/
lemma equivalence_functor :
    (equivalence F G a b ha hb).functor = F.localizedFunctor W.Q V.Q := rfl

/-- 概要：同値の逆関手は指定した相対関手 G の局所化そのもの（Dwyer–Kan）。
方針：局所化の同値の構成の逆関手を評価する。
規約：指定した同じ関手的置換を保持する。
使われ方：E 代数の実際の cofibrant 置換への比較。 -/
lemma equivalence_inverse :
    (equivalence F G a b ha hb).inverse = G.localizedFunctor V.Q W.Q := rfl

end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.RelativeLocalization
