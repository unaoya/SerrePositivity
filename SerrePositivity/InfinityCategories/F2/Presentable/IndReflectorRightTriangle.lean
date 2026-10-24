module

public import SerrePositivity.InfinityCategories.F2.Presentable.IndReflectorCounitIso
public import SerrePositivity.InfinityCategories.F2.Presentable.FunctorHomWhiskering

/-!
概要：専用反映候補の単位と余単位の右三角恒等式。
方針：包含から出る射の Yoneda 制限の単射性で指定単位とその逆を比較する。
規約：同じ元の全自然変換の等式を示す。
使われ方：候補と包含の随伴の検証。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable
open HomotopyLimits Ind
variable {κ : Cardinal.{u}} {C : SSet.{u}} [Quasicategory C]

/-- 概要：元の包含は Indκ の全標準密度余錐を余極限へ送る。
方針：包含した密度余錐を同じ全前層密度余錐へ同定する。
規約：全小余極限の保存は要求しない。
使われ方：包含から出る射の制限の単射性。 -/
lemma indReflectorInclusion_canonicalColimits (v : (IndInfinity κ C) _⦋0⦌) :
    IsColimitCone (leftKanCanonicalCocone (indYoneda κ C)
      (indInclusionPresheaf κ C) v) := by
  apply (indReflectorCanonicalColimits_iff_densityImages (indInclusionPresheaf κ C)).mpr
    (fun w ↦ ?_) v
  exact (F2.isColimitCone_iff_of_cocone_val_eq
    (mapJoinCocone (indInclusionPresheaf κ C) (indVertexDensityCocone κ w))
    (presheafDensityCocone (indVertexPresheaf κ w))
    (indReflectorVertexDensityCocone_val_inclusion w)).mpr (presheafDensityCocone_isColimit _)

variable {L : PresheafInfinity C ⟶ IndInfinity κ C}
    (β : SSet.Homotopy (indYoneda κ C) (yonedaInfinityMap C ≫ L))
    (hβ : IsLeftKanExtension (yonedaInfinityMap C) (indYoneda κ C) L β)

/-- 概要：二つの Yoneda 単位の表示は包含への後合成で両立する。
方針：同じ元の単位の端点の輸送を正規化する。
規約：同型の存在だけでなく同じ射の等式を与える。
使われ方：右三角合成の制限の計算。 -/
lemma indReflectorYonedaUnit_post : indReflectorYonedaUnit β =
    (hoFunctor.map ((ihom ((SSet.uliftFunctor.{u + 1, u}).obj C)).map
      (indInclusionPresheaf κ C))).toFunctor.map
      (indReflectorRestrictionYonedaUnit β) := by
  simp only [indReflectorYonedaUnit, indReflectorRestrictionYonedaUnit,
    F1B.kanFunctorHomCongr, Iso.homCongr, Equiv.coe_fn_mk,
    eqToIso.hom, eqToIso.inv, eqToHom_refl, Category.id_comp, Category.comp_id]

include β hβ in
/-- 概要：指定 Yoneda 単位とその逆を延長する単位・余単位は右三角恒等式を満たす。
方針：包含から出る射を Yoneda 上で比較し、同じ可逆射とその逆を消去する。
規約：元の関手圏内の恒等式である。
使われ方：左三角合成の冪等性と随伴の構成。 -/
lemma indReflector_right_triangle
    (η : FunctorHom (𝟙 (PresheafInfinity C)) (L ≫ indInclusionPresheaf κ C))
    (hη : (hoFunctor.map ((pre (yonedaInfinityMap C)).app (PresheafInfinity C))).toFunctor.map η =
      indReflectorYonedaUnit β)
    (ε : FunctorHom (indInclusionPresheaf κ C ≫ L) (𝟙 (IndInfinity κ C)))
    (hε : (hoFunctor.map ((pre (indYoneda κ C)).app
      (IndInfinity κ C))).toFunctor.map ε =
        indReflectorRestrictionYonedaInverse β hβ) :
    (hoFunctor.map ((pre (indInclusionPresheaf κ C)).app
      (PresheafInfinity C))).toFunctor.map η ≫
      (hoFunctor.map ((ihom (IndInfinity κ C)).map
        (indInclusionPresheaf κ C))).toFunctor.map ε =
          𝟙 (HomotopyCategory.mk (functorVertex (indInclusionPresheaf κ C))) := by
  apply (F1B.kanLeftCanonicalHomMap_bijective (indYoneda κ C)
    (indInclusionPresheaf κ C) indReflectorInclusion_canonicalColimits
    (indInclusionPresheaf κ C)).injective
  have hη' : (hoFunctor.map ((pre (indYoneda κ C ≫
      indInclusionPresheaf κ C)).app (PresheafInfinity C))).toFunctor.map η =
        indReflectorYonedaUnit β := hη
  rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id,
    ← functorHom_pre_comp, hη', functorHom_pre_post, hε,
    indReflectorYonedaUnit_post, ← CategoryTheory.Functor.map_comp]
  have := indReflectorRestrictionYonedaUnit_isIso β hβ
  simp only [indReflectorRestrictionYonedaInverse, IsIso.hom_inv_id,
    CategoryTheory.Functor.map_id]
  rfl

end SerrePositivity.InfinityCategories.F2.Presentable
