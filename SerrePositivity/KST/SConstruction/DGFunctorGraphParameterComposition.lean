module
public import SerrePositivity.KST.SConstruction.DGFunctorGraphParameter
public import SerrePositivity.KST.SConstruction.DGFunctorParamComposition

/-! # 元の graph パラメータ作用の全次数縦合成保存
概要：任意 K・L の入力自然変換の合成は、元の graph 加群 Hom の合成へ送られる。
方針：元の dg Yoneda 関手の全 Hom 合成保存に、二つのパラメータ成分を前合成する。
規約：元の K⊗L と全次数を保持する。使われ方：graph 合成比較の入力横合成。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) (E : Type w)
  [DGCategory A D] [DGCategory A E] [Small.{u} E]

/-- 元の graph の K⊗L パラメータは、同じ二つの graph 成分の全 Hom 合成。 -/
lemma dgFunctorGraphParameter_compose {K L : Complex A} {F G H : DGFunctor A D E}
    (a : DGFunctorParamTrans A D E K F G) (b : DGFunctorParamTrans A D E L G H) (d : D) :
    (dgFunctorGraphParameter A D E (dgFunctorParamCompose A D E a b)).app d =
      ((dgFunctorGraphParameter A D E a).app d ⊗ₘ
        (dgFunctorGraphParameter A D E b).app d) ≫
          moduleComposition A E (representable A (F.obj d)) (representable A (G.obj d))
            (representable A (H.obj d)) := by
  have h := congrArg (fun k => (a.app d ⊗ₘ b.app d) ≫ k)
    ((dgYoneda A E).map_comp (F.obj d) (G.obj d) (H.obj d))
  simp only [dgFunctorGraphParameter_app, dgFunctorParamCompose, dgFunctorFamilyComposeApp,
    Category.assoc, tensorHom_comp_tensorHom_assoc] at h ⊢
  convert h using 1 <;> rfl

end SerrePositivity.KST.SConstruction
