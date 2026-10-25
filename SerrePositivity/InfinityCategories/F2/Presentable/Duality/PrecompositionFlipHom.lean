module

public import SerrePositivity.InfinityCategories.F2.Presentable.Duality.PrecompositionUnit
public import SerrePositivity.InfinityCategories.F2.Presentable.FlipFunctorHomComposition
public import SerrePositivity.InfinityCategories.F2.Presentable.FlipConstantFunctorHom

/-!
概要：前合成の Hom 対応に必要な、転置の合成保存と二つの前合成自然性。
方針：内部 Hom の交換の自然性を h の元の射へ写し、端点の輸送を相殺する。
規約：P のコミット済みの変数交換の公開界面のみを使う。
使われ方：全パラメータの自然な Hom 対応から前合成の全 QCat 随伴を構成する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.F2.Presentable.Duality

/-- 概要：元の Hom の転置は合成を保つ。
方針：コミット済みの変数交換による Hom 同値の合成保存を使う。
規約：元の三つの関手を保持する。
使われ方：前合成の随伴の Hom 対応の自然性。 -/
lemma transposeHomEquiv_comp {A B Z : SSet.{u}} [Quasicategory Z]
    {U V W : A ⟶ (ihom B).obj Z} (α : FunctorHom U V) (β : FunctorHom V W) :
    transposeHomEquiv U W (α ≫ β) =
      transposeHomEquiv U V α ≫ transposeHomEquiv V W β :=
  flipFunctorHomEquiv_comp α β

/-- 概要：関手の始域の前合成による Hom の像は、転置後のパラメータ前合成に一致する。
方針：交換と第二始域への前合成の自然性を h に写し、端点の等式を相殺する。
規約：任意のパラメータ A と任意の二つの関手間の射を扱う。
使われ方：前合成の随伴の両変数の自然性。 -/
lemma transposeHomEquiv_pre_right {A B₀ B Z : SSet.{u}} [Quasicategory Z]
    (j : B₀ ⟶ B) {U V : A ⟶ (ihom B).obj Z} (α : FunctorHom U V) :
    F1B.kanFunctorHomCongr (A := B₀) (D := (ihom A).obj Z)
      (F1B.functorTranspose_pre_right j U) (F1B.functorTranspose_pre_right j V)
      (transposeHomEquiv (A := A) (B := B₀) (Z := Z) (U ≫ (pre j).app Z) (V ≫ (pre j).app Z)
        ((hoFunctor.map ((ihom A).map ((pre j).app Z))).toFunctor.map
          (X := HomotopyCategory.mk (functorVertex U))
          (Y := HomotopyCategory.mk (functorVertex V)) α)) =
    (hoFunctor.map ((pre j).app ((ihom A).obj Z))).toFunctor.map (transposeHomEquiv U V α) := by
  change F1B.kanFunctorHomCongr (A := B₀) (D := (ihom A).obj Z) (F1B.functorTranspose_pre_right j U)
    (F1B.functorTranspose_pre_right j V)
    ((hoFunctor.map (internalHomSwapIso A B₀ Z).hom).toFunctor.map
      ((hoFunctor.map ((ihom A).map ((pre j).app Z))).toFunctor.map
          (X := HomotopyCategory.mk (functorVertex U))
          (Y := HomotopyCategory.mk (functorVertex V)) α)) = _
  have h := CategoryTheory.Functor.congr_hom
    (congrArg (fun f ↦ (hoFunctor.map f).toFunctor) (internalHomSwapIso_pre (A := A) (X := Z) j)) α
  rw [hoFunctor_map_comp_apply] at h
  simp only [F1B.kanFunctorHomCongr, Iso.homCongr_apply, eqToIso.inv, eqToIso.hom]
  rw [h]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_trans, eqToHom_refl,
    Category.id_comp, Category.comp_id]
  exact hoFunctor_map_comp_apply _ _ _

/-- 概要：パラメータ前合成による Hom の像は、転置後の関手の後合成に一致する。
方針：交換と第一始域への前合成の自然性を h に写し、端点の等式を相殺する。
規約：任意のパラメータの射と元の Hom を保持する。
使われ方：前合成の随伴の全パラメータ自然性。 -/
lemma transposeHomEquiv_pre_left {A₀ A B Z : SSet.{u}} [Quasicategory Z]
    (i : A₀ ⟶ A) {U V : A ⟶ (ihom B).obj Z} (α : FunctorHom U V) :
    F1B.kanFunctorHomCongr (A := B) (D := (ihom A₀).obj Z)
      (F1B.functorTranspose_pre_left i U) (F1B.functorTranspose_pre_left i V)
      (transposeHomEquiv (i ≫ U) (i ≫ V)
        ((hoFunctor.map ((pre i).app ((ihom B).obj Z))).toFunctor.map α)) =
    (hoFunctor.map ((ihom B).map ((pre i).app Z))).toFunctor.map (transposeHomEquiv U V α) := by
  change F1B.kanFunctorHomCongr (A := B) (D := (ihom A₀).obj Z) (F1B.functorTranspose_pre_left i U)
    (F1B.functorTranspose_pre_left i V)
    ((hoFunctor.map (internalHomSwapIso A₀ B Z).hom).toFunctor.map
      ((hoFunctor.map ((pre i).app ((ihom B).obj Z))).toFunctor.map α)) = _
  have h := CategoryTheory.Functor.congr_hom
    (congrArg (fun f ↦ (hoFunctor.map f).toFunctor) (F1B.internalHomSwap_pre_left i B Z)) α
  rw [hoFunctor_map_comp_apply] at h
  simp only [F1B.kanFunctorHomCongr, Iso.homCongr_apply, eqToIso.inv, eqToIso.hom]
  rw [h]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_trans, eqToHom_refl,
    Category.id_comp, Category.comp_id]
  exact hoFunctor_map_comp_apply _ _ _

end SerrePositivity.InfinityCategories.F2.Presentable.Duality
