module

public import SerrePositivity.InfinityCategories.F2.Presentable.SigmaReflectorRightTriangle
public import SerrePositivity.InfinityCategories.F1B.Adjunction.UnitLeftTriangle

/-!
概要：全前層圏から P_Σ への専用反映の随伴。
方針：右三角恒等式から左三角合成の冪等性を得て、密度で可逆性を反映する。
規約：一般 Bousfield 局所化を入力にせず、構成済みの同じ候補を用いる。
使われ方：全前層の bar 表示を P_Σ へ反映する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Bicategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable
open HomotopyLimits
variable {C : SSet.{u}} [Quasicategory C]
    {L : PresheafInfinity C ⟶ SigmaPresheafInfinity C}
    (β : SSet.Homotopy (sigmaYonedaInfinityMap C) (yonedaInfinityMap C ≫ L))
    (hβ : IsLeftKanExtension (yonedaInfinityMap C) (sigmaYonedaInfinityMap C) L β)
include β hβ

/-- 概要：指定単位と逆単位を延長した全自然変換は左三角恒等式を満たす。
方針：左三角合成の冪等性と、Yoneda 制限が検出する可逆性を合わせる。
規約：元の関手圏内の恒等式を与える。
使われ方：指定候補と包含の随伴の構成。 -/
lemma sigmaReflector_left_triangle
    (η : FunctorHom (𝟙 (PresheafInfinity C)) (L ≫ sigmaPresheafInfinityInclusion C))
    (hη : (hoFunctor.map ((pre (yonedaInfinityMap C)).app (PresheafInfinity C))).toFunctor.map η =
      sigmaReflectorYonedaUnit β)
    (ε : FunctorHom (sigmaPresheafInfinityInclusion C ≫ L) (𝟙 (SigmaPresheafInfinity C)))
    (hε : (hoFunctor.map ((pre (sigmaYonedaInfinityMap C)).app
      (SigmaPresheafInfinity C))).toFunctor.map ε =
        sigmaReflectorRestrictionYonedaInverse β hβ) :
    unitLeftZigzag η ε = 𝟙 (HomotopyCategory.mk (functorVertex L)) := by
  have hR := sigmaReflector_right_triangle β hβ η hη ε hε
  have hi : IsIso (unitLeftZigzag η ε) := by
    apply functorHom_isIso_of_canonicalRestriction (yonedaInfinityMap C)
      (sigmaReflectorLeftKan_canonicalColimits β hβ)
      (sigmaReflectorLeftKan_canonicalColimits β hβ)
    dsimp only [unitLeftZigzag]
    rw [CategoryTheory.Functor.map_comp, functorHom_pre_post, hη]
    have := sigmaReflectorYonedaUnit_isIso β hβ
    have := sigmaReflector_counit_isIso β hβ ε hε
    infer_instance
  apply (cancel_epi (unitLeftZigzag η ε)).mp
  rw [unitLeftZigzag_idempotent η ε hR, Category.comp_id]

/-- 概要：構成した専用左 Kan 候補は元の包含の左随伴。
方針：密度から単位・余単位を取り、左右の三角恒等式を双圏へ戻す。
規約：同じ候補を保ち、別の反映の存在へ置き換えない。
使われ方：指定 L による bar 表示の反映。 -/
def sigmaReflectorAdjunction : QCatAdjunction L (sigmaPresheafInfinityInclusion C) := by
  let η := Classical.choose (sigmaReflector_exists_unit β)
  have hη := Classical.choose_spec (sigmaReflector_exists_unit β)
  let ε := Classical.choose (sigmaReflector_exists_counit β hβ)
  have hε := Classical.choose_spec (sigmaReflector_exists_counit β hβ)
  refine QCatAdjunction.mkOfHomTriangles
    ((qcatCellEquiv (𝟙 _) (L ≫ sigmaPresheafInfinityInclusion C)).symm η)
    ((qcatCellEquiv (sigmaPresheafInfinityInclusion C ≫ L) (𝟙 _)).symm ε) ?_ ?_
  · rw [qcatLeftZigzag_hom]
    simp only [Strict.leftUnitor_eqToIso, Strict.rightUnitor_eqToIso,
      eqToIso.hom, eqToIso.inv, eqToHom_refl, Category.id_comp]
    exact (sigmaReflector_left_triangle β hβ η hη ε hε).trans
      ((qcatHomFunctor _ _).map_id (qcatMap L)).symm
  · rw [qcatRightZigzag_hom]
    simp only [Strict.leftUnitor_eqToIso, Strict.rightUnitor_eqToIso,
      eqToIso.hom, eqToIso.inv, eqToHom_refl, Category.id_comp]
    exact (sigmaReflector_right_triangle β hβ η hη ε hε).trans
      ((qcatHomFunctor _ _).map_id (qcatMap (sigmaPresheafInfinityInclusion C))).symm

omit β hβ in
/-- 概要：有限余積を持つ底に対する P_Σ 専用反映が存在する。
方針：小余積と幾何学的実現で構成した候補に同じ随伴を付ける。
規約：一般局所化や他レーンの追加供給を要求しない。
使われ方：P_Σ の simplicial Ind 表示と小余極限。
-/
lemma sigma_exists_reflector
    (hC : ∀ (J : Type u) [Finite J] (p : nerve (Discrete J) ⟶ C.op), HasLimit p) :
    ∃ L : PresheafInfinity C ⟶ SigmaPresheafInfinity C,
      Nonempty (QCatAdjunction L (sigmaPresheafInfinityInclusion C)) := by
  obtain ⟨L, β, hβ⟩ := sigma_exists_reflectorLeftKan hC
  exact ⟨L, ⟨sigmaReflectorAdjunction β hβ⟩⟩

end SerrePositivity.InfinityCategories.F2.Presentable
