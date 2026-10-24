module

public import SerrePositivity.InfinityCategories.F2.Presentable.CoconeUnitHomUniversal
public import SerrePositivity.InfinityCategories.F2.Presentable.FlipConstantFunctorHom
public import SerrePositivity.InfinityCategories.HomotopyLimits.ParameterUnitHom

/-!
概要：転置した Hom 公式を普遍余錐へ照合して Hom 全単射を得る。
方針：頂点表示と変数交換の二つの同値で普遍余錐の全単射を輸送する。
規約：余極限関手の具体的な選択に依存しない。
使われ方：選んだ余極限単位の全パラメータ判定。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable

/-- 概要：転置した Hom 公式が普遍余錐の単位公式なら元の Hom 写像は全単射。
方針：二つの同値で両端を輸送し、元の余錐の全単射を適用する。
規約：同じ全余錐と指定写像を保つ。
使われ方：余極限関手の随伴の単位判定。 -/
lemma colimitUnitHom_bijective_of_flip {K A X : SSet.{u}} [Quasicategory X]
    {U : A ⟶ (ihom K).obj X} {L V : A ⟶ X}
    (c : JoinCocone (internalHomFlipHomEquiv A K X U)) (hc : IsColimitCone c)
    (hL : c.vertex = functorVertex L)
    (f : FunctorHom L V → FunctorHom U (V ≫ constantFunctorMap K X))
    (hf : ∀ α, F1B.kanFunctorHomCongr rfl (flip_postcompose_constant V)
      (flipFunctorHomEquiv U (V ≫ constantFunctorMap K X) (f α)) =
      coconeUnitHom c ≫ constantFunctorHomMap K (eqToHom (congrArg HomotopyCategory.mk hL) ≫ α)) :
    Function.Bijective f := by
  let e := (flipFunctorHomEquiv U (V ≫ constantFunctorMap K X)).trans
    (F1B.kanFunctorHomCongr rfl (flip_postcompose_constant V))
  let a := Iso.homCongr (eqToIso (congrArg HomotopyCategory.mk hL)).symm
    (Iso.refl (HomotopyCategory.mk (functorVertex V)))
  have hb := (coconeUnitHom_bijective c hc (functorVertex V)).comp a.bijective
  have h : Function.Bijective (e ∘ f) := by
    convert hb using 1
    funext α
    simpa only [e, a, Function.comp_apply, Equiv.trans_apply, Iso.homCongr_apply,
      Iso.symm_inv, eqToIso.hom, Iso.refl_hom, Category.comp_id] using hf α
  exact h.of_comp_left e.injective

/-- 概要：任意パラメータ版の単位 Hom 全単射と quasicategory 版は同値。
方針：指定写像の点ごとの一致を使う。
規約：同じ単位を保持する。
使われ方：普遍余錐から随伴の単位判定へ移す。 -/
lemma parameterUnitHomMap_bijective_iff {A X Y : SSet.{u}}
    [Quasicategory A] [Quasicategory X] [Quasicategory Y]
    {F : X ⟶ Y} {G : Y ⟶ X} (η : FunctorHom (𝟙 X) (F ≫ G))
    (U : A ⟶ X) (V : A ⟶ Y) :
    Function.Bijective (HomotopyLimits.parameterUnitHomMap η U V) ↔
      Function.Bijective (qcatUnitHomMap η U V) := by
  have h := funext (HomotopyLimits.parameterUnitHomMap_eq η U V)
  rw [h]

end SerrePositivity.InfinityCategories.F2.Presentable
