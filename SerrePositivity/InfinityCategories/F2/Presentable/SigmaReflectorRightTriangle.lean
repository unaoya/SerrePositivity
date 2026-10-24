module

public import SerrePositivity.InfinityCategories.F2.Presentable.SigmaReflectorCounitIso
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
variable {C : SSet.{u}} [Quasicategory C]

/-- 概要：元の包含は P_Σ の全標準密度余錐を余極限へ送る。
方針：包含した密度余錐を同じ全前層密度余錐へ同定する。
規約：全小余極限の保存は要求しない。
使われ方：包含から出る射の制限の単射性。 -/
lemma sigmaInclusion_canonicalColimits (v : (SigmaPresheafInfinity C) _⦋0⦌) :
    IsColimitCone (leftKanCanonicalCocone (sigmaYonedaInfinityMap C)
      (sigmaPresheafInfinityInclusion C) v) := by
  apply (sigmaCanonicalColimits_iff_densityImages (sigmaPresheafInfinityInclusion C)).mpr
    (fun w ↦ ?_) v
  exact (F2.isColimitCone_iff_of_cocone_val_eq
    (mapJoinCocone (sigmaPresheafInfinityInclusion C) (sigmaVertexDensityCocone w))
    (presheafDensityCocone (sigmaPresheafVertexFunctor w))
    (sigmaVertexDensityCocone_val_inclusion w)).mpr (presheafDensityCocone_isColimit _)

variable {L : PresheafInfinity C ⟶ SigmaPresheafInfinity C}
    (β : SSet.Homotopy (sigmaYonedaInfinityMap C) (yonedaInfinityMap C ≫ L))
    (hβ : IsLeftKanExtension (yonedaInfinityMap C) (sigmaYonedaInfinityMap C) L β)

/-- 概要：二つの Yoneda 単位の表示は包含への後合成で両立する。
方針：同じ元の単位の端点の輸送を正規化する。
規約：同型の存在だけでなく同じ射の等式を与える。
使われ方：右三角合成の制限の計算。 -/
lemma sigmaReflectorYonedaUnit_post : sigmaReflectorYonedaUnit β =
    (hoFunctor.map ((ihom ((SSet.uliftFunctor.{u + 1, u}).obj C)).map
      (sigmaPresheafInfinityInclusion C))).toFunctor.map
      (sigmaReflectorRestrictionYonedaUnit β) := by
  simp only [sigmaReflectorYonedaUnit, sigmaReflectorRestrictionYonedaUnit,
    F1B.kanFunctorHomCongr, Iso.homCongr, Equiv.coe_fn_mk,
    eqToIso.hom, eqToIso.inv, eqToHom_refl, Category.id_comp, Category.comp_id]

include β hβ in
/-- 概要：指定 Yoneda 単位とその逆を延長する単位・余単位は右三角恒等式を満たす。
方針：包含から出る射を Yoneda 上で比較し、同じ可逆射とその逆を消去する。
規約：元の関手圏内の恒等式である。
使われ方：左三角合成の冪等性と随伴の構成。 -/
lemma sigmaReflector_right_triangle
    (η : FunctorHom (𝟙 (PresheafInfinity C)) (L ≫ sigmaPresheafInfinityInclusion C))
    (hη : (hoFunctor.map ((pre (yonedaInfinityMap C)).app (PresheafInfinity C))).toFunctor.map η =
      sigmaReflectorYonedaUnit β)
    (ε : FunctorHom (sigmaPresheafInfinityInclusion C ≫ L) (𝟙 (SigmaPresheafInfinity C)))
    (hε : (hoFunctor.map ((pre (sigmaYonedaInfinityMap C)).app
      (SigmaPresheafInfinity C))).toFunctor.map ε =
        sigmaReflectorRestrictionYonedaInverse β hβ) :
    (hoFunctor.map ((pre (sigmaPresheafInfinityInclusion C)).app
      (PresheafInfinity C))).toFunctor.map η ≫
      (hoFunctor.map ((ihom (SigmaPresheafInfinity C)).map
        (sigmaPresheafInfinityInclusion C))).toFunctor.map ε =
          𝟙 (HomotopyCategory.mk (functorVertex (sigmaPresheafInfinityInclusion C))) := by
  apply (F1B.kanLeftCanonicalHomMap_bijective (sigmaYonedaInfinityMap C)
    (sigmaPresheafInfinityInclusion C) sigmaInclusion_canonicalColimits
    (sigmaPresheafInfinityInclusion C)).injective
  have hη' : (hoFunctor.map ((pre (sigmaYonedaInfinityMap C ≫
      sigmaPresheafInfinityInclusion C)).app (PresheafInfinity C))).toFunctor.map η =
        sigmaReflectorYonedaUnit β := hη
  rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id,
    ← functorHom_pre_comp, hη', functorHom_pre_post, hε,
    sigmaReflectorYonedaUnit_post, ← CategoryTheory.Functor.map_comp]
  have := sigmaReflectorRestrictionYonedaUnit_isIso β hβ
  simp only [sigmaReflectorRestrictionYonedaInverse, IsIso.hom_inv_id,
    CategoryTheory.Functor.map_id]
  rfl

end SerrePositivity.InfinityCategories.F2.Presentable
