module

public import SerrePositivity.InfinityCategories.F2.Presentable.ConeFamilyCounitSwap
public import SerrePositivity.InfinityCategories.F2.Presentable.FlipFunctorHomComposition

/-!
概要：全極限錐族の余単位が与える Hom 対応を全単射として保持する。
方針：変数交換と native な普遍錐の Hom 全単射を結合する。
規約：全錐族とその指定した余単位を変更しない。
使われ方：随伴による比較射の可逆性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable

/-- 概要：定値後合成に続く全射の転置は、元の Hom の定値化との合成。
方針：交換と端点輸送の合成保存を使う。
規約：余単位に随伴条件や可逆性を課さない。
使われ方：元の錐の余単位の全 Hom 公式。 -/
lemma flip_constant_composite_hom {A K X : SSet.{u}} [Quasicategory X]
    {U : A ⟶ (ihom K).obj X} {L V : A ⟶ X}
    (t : FunctorHom (L ≫ constantFunctorMap K X) U) (α : FunctorHom V L) :
    F1B.kanFunctorHomCongr (flip_postcompose_constant V) rfl
      (flipFunctorHomEquiv (V ≫ constantFunctorMap K X) U
        ((hoFunctor.map ((ihom A).map (constantFunctorMap K X))).toFunctor.map α ≫ t)) =
    constantFunctorHomMap K α ≫
      F1B.kanFunctorHomCongr (flip_postcompose_constant L) rfl
        (flipFunctorHomEquiv (L ≫ constantFunctorMap K X) U t) := by
  let b : FunctorHom (V ≫ constantFunctorMap K X) (L ≫ constantFunctorMap K X) :=
    (hoFunctor.map ((ihom A).map (constantFunctorMap K X))).toFunctor.map α
  change F1B.kanFunctorHomCongr (flip_postcompose_constant V) rfl
    (flipFunctorHomEquiv (V ≫ constantFunctorMap K X) U (b ≫ t)) = _
  rw [flipFunctorHomEquiv_comp,
    functorHomCongr_comp (flip_postcompose_constant V) (flip_postcompose_constant L) rfl]
  exact congrArg (· ≫ F1B.kanFunctorHomCongr (flip_postcompose_constant L) rfl
    (flipFunctorHomEquiv (L ≫ constantFunctorMap K X) U t))
      (flip_postcompose_constant_hom (K := K) α)

/-- 概要：全極限錐族の指定余単位による全 Hom 写像は全単射。
方針：元の全錐を関手圏の普遍錐に転置し、頂点表示の同型で Hom 対応を移す。
規約：任意のパラメータ A を全次数で保持する。
使われ方：定値図式の右随伴への全自然な比較の可逆性。 -/
lemma coneFamilyCounitHom_bijective {A K X : SSet.{u}} [Quasicategory X]
    (s : A ⟶ (ihom (join Δ[0] K)).obj X)
    (hs : ∀ a : A _⦋0⦌, IsLimitCone (functorVertexCone (s.app (Opposite.op ⦋0⦌) a)))
    (V : A ⟶ X) :
    Function.Bijective (fun α : FunctorHom V
      (s ≫ evaluateFunctorAt (SSet.yonedaEquiv (joinInl Δ[0] K))) ↦
      (hoFunctor.map ((ihom A).map (constantFunctorMap K X))).toFunctor.map α ≫
        coneFunctorCounitHom s) := by
  let L := s ≫ evaluateFunctorAt (SSet.yonedaEquiv (joinInl Δ[0] K))
  let U := s ≫ (pre (joinInr Δ[0] K)).app X
  let c := pointwiseLimitFamilyCone s
  have hc : IsLimitCone c := pointwiseLimitFamilyCone_isLimit s hs
  have hL : c.vertex = functorVertex L := pointwiseLimitFamilyCone_vertex s
  let e := (flipFunctorHomEquiv (V ≫ constantFunctorMap K X) U).trans
    (F1B.kanFunctorHomCongr (flip_postcompose_constant V) rfl)
  let a : FunctorHom V L ≃
      ((HomotopyCategory.mk (functorVertex V) : hoFunctor.obj ((ihom A).obj X)) ⟶
        HomotopyCategory.mk c.vertex) :=
    (Iso.refl _).homCongr (eqToIso (congrArg HomotopyCategory.mk hL)).symm
  have hb := (coneCounitHom_bijective c hc (functorVertex V)).comp a.bijective
  let f := fun α : FunctorHom V L ↦
    (hoFunctor.map ((ihom A).map (constantFunctorMap K X))).toFunctor.map α ≫
      coneFunctorCounitHom s
  have h : Function.Bijective (e ∘ f) := by
    convert hb using 1
    funext α
    change F1B.kanFunctorHomCongr (flip_postcompose_constant V) rfl
      (flipFunctorHomEquiv (V ≫ constantFunctorMap K X) U
        ((hoFunctor.map ((ihom A).map (constantFunctorMap K X))).toFunctor.map α ≫
          coneFunctorCounitHom s)) = _
    rw [flip_constant_composite_hom, coneFamilyCounitHom_swap]
    simp only [a, Function.comp_apply, Iso.homCongr_apply, Iso.refl_inv, Iso.symm_hom,
      eqToIso.inv, Category.id_comp, constantFunctorHomMap_comp,
      F1B.kanFunctorHomCongr, eqToIso.hom,
      Category.assoc]
    erw [constantFunctorHomMap_eqToHom]
    · simp only [c, eqToHom_refl, Category.comp_id]
      rfl
    · exact hL.symm
  exact h.of_comp_left e.injective

end SerrePositivity.InfinityCategories.F2.Presentable
