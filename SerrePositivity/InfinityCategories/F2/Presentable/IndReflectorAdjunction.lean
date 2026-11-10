module

public import SerrePositivity.InfinityCategories.F2.Presentable.IndReflectorRightTriangle
public import SerrePositivity.InfinityCategories.F1B.Adjunction.UnitLeftTriangle

/-!
概要：全前層圏から Indκ への専用反映の随伴。
方針：右三角恒等式から左三角合成の冪等性を得て、密度で可逆性を反映する。
規約：一般 Bousfield 局所化を入力にせず、構成済みの同じ候補を用いる。
使われ方：Indκ の極限と前層による余極限計算。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Bicategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable
open HomotopyLimits Ind
variable {κ : Cardinal.{u}} {C : SSet.{u}} [Quasicategory C]
    {L : PresheafInfinity C ⟶ IndInfinity κ C}
    (β : SSet.Homotopy (indYoneda κ C) (yonedaInfinityMap C ≫ L))
    (hβ : IsLeftKanExtension (yonedaInfinityMap C) (indYoneda κ C) L β)
include β hβ

/-- 概要：指定単位と逆単位を延長した全自然変換は左三角恒等式を満たす。
方針：左三角合成の冪等性と、Yoneda 制限が検出する可逆性を合わせる。
規約：元の関手圏内の恒等式を与える。
使われ方：指定候補と包含の随伴の構成。 -/
lemma indReflector_left_triangle
    (η : FunctorHom (𝟙 (PresheafInfinity C)) (L ≫ indInclusionPresheaf κ C))
    (hη : (hoFunctor.map ((pre (yonedaInfinityMap C)).app (PresheafInfinity C))).toFunctor.map η =
      indReflectorYonedaUnit β)
    (ε : FunctorHom (indInclusionPresheaf κ C ≫ L) (𝟙 (IndInfinity κ C)))
    (hε : (hoFunctor.map ((pre (indYoneda κ C)).app
      (IndInfinity κ C))).toFunctor.map ε =
        indReflectorRestrictionYonedaInverse β hβ) :
    unitLeftZigzag η ε = 𝟙 (HomotopyCategory.mk (functorVertex L)) := by
  have hR := indReflector_right_triangle β hβ η hη ε hε
  have hi : IsIso (unitLeftZigzag η ε) := by
    apply functorHom_isIso_of_canonicalRestriction (yonedaInfinityMap C)
      (presheafYonedaLeftKan_canonicalColimits β hβ)
      (presheafYonedaLeftKan_canonicalColimits β hβ)
    dsimp only [unitLeftZigzag]
    rw [CategoryTheory.Functor.map_comp, functorHom_pre_post, hη]
    have := indReflectorYonedaUnit_isIso β hβ
    have := indReflector_counit_isIso β hβ ε hε
    infer_instance
  apply (cancel_epi (unitLeftZigzag η ε)).mp
  rw [unitLeftZigzag_idempotent η ε hR, Category.comp_id]

/-- 概要：構成した専用左 Kan 候補は元の包含の左随伴。
方針：密度から単位・余単位を取り、左右の三角恒等式を双圏へ戻す。
規約：同じ候補を保ち、別の反映の存在へ置き換えない。
使われ方：指定 L による bar 表示の反映。 -/
def indReflectorAdjunction : QCatAdjunction L (indInclusionPresheaf κ C) := by
  let η := Classical.choose (indReflector_exists_unit β)
  have hη := Classical.choose_spec (indReflector_exists_unit β)
  let ε := Classical.choose (indReflector_exists_counit β hβ)
  have hε := Classical.choose_spec (indReflector_exists_counit β hβ)
  refine QCatAdjunction.mkOfHomTriangles
    ((qcatCellEquiv (𝟙 _) (L ≫ indInclusionPresheaf κ C)).symm η)
    ((qcatCellEquiv (indInclusionPresheaf κ C ≫ L) (𝟙 _)).symm ε) ?_ ?_
  · rw [qcatLeftZigzag_hom]
    simp only [Strict.leftUnitor_eqToIso, Strict.rightUnitor_eqToIso,
      eqToIso.hom, eqToIso.inv, eqToHom_refl, Category.id_comp]
    exact (indReflector_left_triangle β hβ η hη ε hε).trans
      ((qcatHomFunctor _ _).map_id (qcatMap L)).symm
  · rw [qcatRightZigzag_hom]
    simp only [Strict.leftUnitor_eqToIso, Strict.rightUnitor_eqToIso,
      eqToIso.hom, eqToIso.inv, eqToHom_refl, Category.id_comp]
    exact (indReflector_right_triangle β hβ η hη ε hε).trans
      ((qcatHomFunctor _ _).map_id (qcatMap (indInclusionPresheaf κ C))).symm

omit β hβ in
/-- 概要：余完備な Indκ への前層反映が存在する。
方針：前層 Yoneda の左 Kan 候補に同じ随伴を付ける。
規約：一般局所化や他レーンの追加供給を要求しない。
使われ方：Indκ の小極限と反映による余極限計算。
-/
lemma ind_exists_presheafReflector
    (hD : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.HasSmallColimits (IndInfinity κ C)) :
    ∃ L : PresheafInfinity C ⟶ IndInfinity κ C,
      Nonempty (QCatAdjunction L (indInclusionPresheaf κ C)) := by
  obtain ⟨L, β, hβ⟩ := presheaf_exists_yonedaLeftKan hD (indYoneda κ C)
  exact ⟨L, ⟨indReflectorAdjunction β hβ⟩⟩

end SerrePositivity.InfinityCategories.F2.Presentable
