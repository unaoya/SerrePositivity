module

public import SerrePositivity.InfinityCategories.F1B.KanNerveAdjunction
public import SerrePositivity.InfinityCategories.F1B.KanNerveNatTransRecovery
public import SerrePositivity.InfinityCategories.F1B.KanAdjunctionHomTriangles

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
namespace SerrePositivity.InfinityCategories.F1B

/-- 概要：指定した nerve 関手間の随伴から元の通常の関手間の随伴を復元する。
方針：自然変換の全単射で単位・余単位を戻し忠実性で三角恒等式を反映する。
規約：hC と hD だけの随伴からの推論に置き換えない。
使われ方：B5 の古典随伴の回収の逆方向。 -/
def kanAdjunctionOfNerveAdjunction {C D : Type u} [Category.{u} C] [Category.{u} D]
    {F : C ⥤ D} {G : D ⥤ C} (a : QCatAdjunction (nerveMap F) (nerveMap G)) : F ⊣ G := by
  let η := (kanNerveNatTransHomEquiv (𝟭 C) (F ⋙ G)).symm a.unitHom
  let ε := (kanNerveNatTransHomEquiv (G ⋙ F) (𝟭 D)).symm a.counitHom
  have hη : kanNerveNatTransHom η = a.unitHom :=
    (kanNerveNatTransHomEquiv (𝟭 C) (F ⋙ G)).apply_symm_apply a.unitHom
  have hε : kanNerveNatTransHom ε = a.counitHom :=
    (kanNerveNatTransHomEquiv (G ⋙ F) (𝟭 D)).apply_symm_apply a.counitHom
  have hL : CategoryTheory.Functor.whiskerRight η F ≫
      CategoryTheory.Functor.whiskerLeft F ε = 𝟙 F := by
    apply (kanNerveFunctorHomEmbedding_fullyFaithful C D).map_injective
    change kanNerveNatTransHom (_ ≫ _) = kanNerveNatTransHom (𝟙 F)
    rw [kanNerveNatTransHom_comp, ← kanNerveNatTransHom_whiskerRight,
      ← kanNerveNatTransHom_whiskerLeft, kanNerveNatTransHom_id, hη, hε]
    exact kanAdjunction_leftTriangleHom a
  have hR : CategoryTheory.Functor.whiskerLeft G η ≫
      CategoryTheory.Functor.whiskerRight ε G = 𝟙 G := by
    apply (kanNerveFunctorHomEmbedding_fullyFaithful D C).map_injective
    change kanNerveNatTransHom (_ ≫ _) = kanNerveNatTransHom (𝟙 G)
    rw [kanNerveNatTransHom_comp, ← kanNerveNatTransHom_whiskerLeft,
      ← kanNerveNatTransHom_whiskerRight, kanNerveNatTransHom_id, hη, hε]
    exact kanAdjunction_rightTriangleHom a
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
lemma kanAdjunctionOfNerveAdjunction_unitHom {C D : Type u}
    [Category.{u} C] [Category.{u} D] {F : C ⥤ D} {G : D ⥤ C}
    (a : QCatAdjunction (nerveMap F) (nerveMap G)) :
    kanNerveNatTransHom (kanAdjunctionOfNerveAdjunction a).unit = a.unitHom :=
  (kanNerveNatTransHomEquiv (𝟭 C) (F ⋙ G)).apply_symm_apply a.unitHom

/-- 概要：復元した通常の随伴の余単位は元の nerve 随伴の余単位を表す。
方針：全単射の逆写像の表示を読む。
規約：元の余単位の類を保つ。
使われ方：古典随伴の双方向の比較。 -/
lemma kanAdjunctionOfNerveAdjunction_counitHom {C D : Type u}
    [Category.{u} C] [Category.{u} D] {F : C ⥤ D} {G : D ⥤ C}
    (a : QCatAdjunction (nerveMap F) (nerveMap G)) :
    kanNerveNatTransHom (kanAdjunctionOfNerveAdjunction a).counit = a.counitHom :=
  (kanNerveNatTransHomEquiv (G ⋙ F) (𝟭 D)).apply_symm_apply a.counitHom

/-- 概要：通常の関手間の随伴の存在は元の nerve 間の随伴の存在と同値。
方針：指定単位・余単位を保つ二つの構成を使う。
規約：同じ宇宙の小さい圏についての存在命題。
使われ方：B5 の古典随伴の回収。 -/
lemma kanNonempty_adjunction_iff_nerveAdjunction {C D : Type u}
    [Category.{u} C] [Category.{u} D] (F : C ⥤ D) (G : D ⥤ C) :
    Nonempty (F ⊣ G) ↔ Nonempty (QCatAdjunction (nerveMap F) (nerveMap G)) :=
  ⟨fun ⟨a⟩ ↦ ⟨kanNerveAdjunctionOfAdjunction a⟩,
    fun ⟨a⟩ ↦ ⟨kanAdjunctionOfNerveAdjunction a⟩⟩

end SerrePositivity.InfinityCategories.F1B
