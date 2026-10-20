module
public import SerrePositivity.KST.SConstruction.DGParameterPullback

/-! # パラメータ引き戻しと元の入力 Hom end
概要：任意 K 自然変換を、元の Hom end の普遍自然変換の引き戻しとして回収する。
方針：全対象評価で元の Hom end の普遍性を適用する。
規約：出力の巨大な end を導入しない。使われ方：全入力 Hom の作用の因子化。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) (E : Type w)
  [DGCategory A D] [Small.{u} D] [DGCategory A E] (F G : DGFunctor A D E)

/-- 元の Hom end のパラメータ表示は、パラメータ複体の射に関して自然。 -/
lemma dgFunctorHomEquiv_pullback {K L : Complex A} (a : L ⟶ K)
    (f : K ⟶ dgFunctorHom A D E F G) :
    dgFunctorHomEquiv A D E L F G (a ≫ f) =
      dgParameterPullback A a (dgFunctorHomEquiv A D E K F G f) := by
  apply GradedNatTrans.ext
  funext d
  exact Category.assoc _ _ _

/-- 逆向きの Hom end 表示も、同じパラメータ引き戻しを前合成として回収する。 -/
lemma dgFunctorHomEquiv_symm_pullback {K L : Complex A} (a : L ⟶ K)
    (τ : DGFunctorParamTrans A D E K F G) :
    (dgFunctorHomEquiv A D E L F G).symm (dgParameterPullback A a τ) =
      a ≫ (dgFunctorHomEquiv A D E K F G).symm τ := by
  apply dgFunctorHom_ext
  intro d
  rw [dgFunctorHomEquiv_symm_π, Category.assoc, dgFunctorHomEquiv_symm_π]
  rfl

/-- 任意の入力自然変換は、元の入力 Hom の普遍自然変換の同じ引き戻しである。 -/
lemma dgParameterUniversal_pullback {K : Complex A}
    (τ : DGFunctorParamTrans A D E K F G) :
    dgParameterPullback A ((dgFunctorHomEquiv A D E K F G).symm τ)
        (dgFunctorHomEquiv A D E (dgFunctorHom A D E F G) F G (𝟙 _)) = τ := by
  apply GradedNatTrans.ext
  funext d
  change (dgFunctorHomEquiv A D E K F G).symm τ ≫
    (𝟙 _ ≫ dgFunctorHomπ A D E F G d) = τ.app d
  rw [Category.id_comp, dgFunctorHomEquiv_symm_π]

end SerrePositivity.KST.SConstruction
