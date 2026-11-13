module

public import SerrePositivity.InfinityCategories.HTT.Section5_2_5.Adjunction
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.NatTransRecovery
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.AdjunctionHomTriangles

/-!
概要：通常の関手の随伴を元の nerve 間の随伴から回収する。
方針：自然変換の全単射と左右 whiskering の保存で三角恒等式を反映する。
規約：元の単位・余単位を復元する。
使われ方：B5 の古典随伴の双方向の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Bicategory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison

/-- 概要：指定した nerve 関手間の随伴から元の通常の関手間の随伴を復元する。
方針：自然変換の全単射で単位・余単位を戻し忠実性で三角恒等式を反映する。
規約：hC と hD だけの随伴からの推論に置き換えない。
使われ方：B5 の古典随伴の回収の逆方向。 -/
def adjunctionOfNerveAdjunction {C D : Type u} [Category.{u} C] [Category.{u} D]
    {F : C ⥤ D} {G : D ⥤ C} (a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction (nerveMap F) (nerveMap G)) : F ⊣ G := by
  let η := (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveNatTransHomEquiv (𝟭 C) (F ⋙ G)).symm a.unitHom
  let ε := (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveNatTransHomEquiv (G ⋙ F) (𝟭 D)).symm a.counitHom
  have hη : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveNatTransHom η = a.unitHom :=
    (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveNatTransHomEquiv (𝟭 C) (F ⋙ G)).apply_symm_apply a.unitHom
  have hε : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveNatTransHom ε = a.counitHom :=
    (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveNatTransHomEquiv (G ⋙ F) (𝟭 D)).apply_symm_apply a.counitHom
  have hL : CategoryTheory.Functor.whiskerRight η F ≫
      CategoryTheory.Functor.whiskerLeft F ε = 𝟙 F := by
    apply (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveFunctorHomEmbedding_fullyFaithful C D).map_injective
    change _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveNatTransHom (_ ≫ _) = _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveNatTransHom (𝟙 F)
    rw [_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveNatTransHom_comp, ← _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveNatTransHom_whiskerRight,
      ← _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveNatTransHom_whiskerLeft, _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveNatTransHom_id, hη, hε]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.adjunction_leftTriangleHom a
  have hR : CategoryTheory.Functor.whiskerLeft G η ≫
      CategoryTheory.Functor.whiskerRight ε G = 𝟙 G := by
    apply (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveFunctorHomEmbedding_fullyFaithful D C).map_injective
    change _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveNatTransHom (_ ≫ _) = _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveNatTransHom (𝟙 G)
    rw [_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveNatTransHom_comp, ← _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveNatTransHom_whiskerLeft,
      ← _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveNatTransHom_whiskerRight, _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveNatTransHom_id, hη, hε]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.adjunction_rightTriangleHom a
  refine Adjunction.mkOfUnitCounit
    { unit := η
      counit := ε
      left_triangle := ?_
      right_triangle := ?_ }
  · ext x
    simpa using NatTrans.congr_app hL x
  · ext x
    simpa using NatTrans.congr_app hR x

/-- 概要：復元した通常の随伴の単位は元の nerve 随伴の単位を表す。
方針：自然変換の全単射の逆性を使う。
規約：元の単位の類をそのまま復元する。
使われ方：指定データを保つ随伴の比較。 -/
lemma adjunctionOfNerveAdjunction_unitHom {C D : Type u}
    [Category.{u} C] [Category.{u} D] {F : C ⥤ D} {G : D ⥤ C}
    (a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction (nerveMap F) (nerveMap G)) :
    _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveNatTransHom (adjunctionOfNerveAdjunction a).unit = a.unitHom :=
  (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveNatTransHomEquiv (𝟭 C) (F ⋙ G)).apply_symm_apply a.unitHom

/-- 概要：復元した通常の随伴の余単位は元の nerve 随伴の余単位を表す。
方針：全単射の逆写像の表示を読む。
規約：元の余単位の類を保つ。
使われ方：古典随伴の双方向の比較。 -/
lemma adjunctionOfNerveAdjunction_counitHom {C D : Type u}
    [Category.{u} C] [Category.{u} D] {F : C ⥤ D} {G : D ⥤ C}
    (a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction (nerveMap F) (nerveMap G)) :
    _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveNatTransHom (adjunctionOfNerveAdjunction a).counit = a.counitHom :=
  (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveNatTransHomEquiv (G ⋙ F) (𝟭 D)).apply_symm_apply a.counitHom

/-- 概要：通常の関手間の随伴の存在は元の nerve 間の随伴の存在と同値。
方針：指定単位・余単位を保つ二つの構成を使う。
規約：同じ宇宙の小さい圏についての存在命題。
使われ方：B5 の古典随伴の回収。 -/
lemma nonempty_adjunction_iff_nerveAdjunction {C D : Type u}
    [Category.{u} C] [Category.{u} D] (F : C ⥤ D) (G : D ⥤ C) :
    Nonempty (F ⊣ G) ↔ Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction (nerveMap F) (nerveMap G)) :=
  ⟨fun ⟨a⟩ ↦ ⟨_root_.SerrePositivity.InfinityCategories.HTT.Section5_2_5.nerveAdjunctionOfAdjunction a⟩,
    fun ⟨a⟩ ↦ ⟨adjunctionOfNerveAdjunction a⟩⟩

end SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison
