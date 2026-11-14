module

public import SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.CrystallineExtraPolynomial
public import Mathlib.RingTheory.TensorProduct.Maps
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.CrystallineExtraModel
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.CrystallineExtraPolynomial
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Poincare.CrystallineExtraContraction
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.PDPolynomialCech

/-!
# 高次 δ 座標つき pd 模型のテンソル表示

## 概要
係数環の下で取った余積を通常のテンソル積で表す。

## 方針
両側の標準射を保つ同型を、テンソル積と余積の普遍性から作る。

## 規約
右因子は高次座標の多項式環。

## 使われ方
未完備結晶模型の座標分離。
-/

public noncomputable section

open CategoryTheory CategoryTheory.Limits Algebra.TensorProduct
open scoped TensorProduct
universe u

namespace SerrePositivity.BhattScholze.Prismatic

section Under

variable {R : CommRingCat.{u}}

private theorem underCoprod_isPushout (X Y : Under R) :
    IsPushout X.hom Y.hom
      (coprod.inl : X ⟶ X ⨿ Y).right (coprod.inr : Y ⟶ X ⨿ Y).right := by
  have w : X.hom ≫ (coprod.inl : X ⟶ X ⨿ Y).right =
      Y.hom ≫ (coprod.inr : Y ⟶ X ⨿ Y).right :=
    (Under.w _).trans (Under.w _).symm
  refine IsPushout.of_isColimit' ⟨w⟩ (PushoutCocone.isColimitAux' _ fun S => ?_)
  let Z := Under.mk (X.hom ≫ S.inl)
  let f : X ⟶ Z := Under.homMk S.inl rfl
  let g : Y ⟶ Z := Under.homMk S.inr S.condition.symm
  let h := coprod.desc f g
  refine ⟨h.right, ?_, ?_, ?_⟩
  · exact congrArg Under.Hom.right (coprod.inl_desc f g)
  · exact congrArg Under.Hom.right (coprod.inr_desc f g)
  · intro l hl hr
    have hL : (X ⨿ Y).hom ≫ l = Z.hom := by
      rw [← Under.w (coprod.inl : X ⟶ X ⨿ Y), Category.assoc]
      exact congrArg (X.hom ≫ ·) hl
    let j : X ⨿ Y ⟶ Z := Under.homMk l hL
    have hj : j = h := by
      apply coprod.hom_ext
      · apply Under.UnderMorphism.ext
        exact hl.trans (congrArg Under.Hom.right (coprod.inl_desc f g)).symm
      · apply Under.UnderMorphism.ext
        exact hr.trans (congrArg Under.Hom.right (coprod.inr_desc f g)).symm
    exact congrArg Under.Hom.right hj

variable (R) (X Y : Type u) [CommRing X] [CommRing Y] [Algebra R X] [Algebra R Y]

private def underTensorIso :
    CommRingCat.of (X ⊗[R] Y) ≅ (CommRingCat.mkUnder R X ⨿ CommRingCat.mkUnder R Y).right :=
  (CommRingCat.isPushout_tensorProduct R X Y).isoPushout ≪≫
    (underCoprod_isPushout (CommRingCat.mkUnder R X) (CommRingCat.mkUnder R Y)).isoPushout.symm

private theorem underTensorIso_inl :
    CommRingCat.ofHom (S := X ⊗[R] Y) Algebra.TensorProduct.includeLeftRingHom ≫
      (underTensorIso R X Y).hom =
        (coprod.inl : CommRingCat.mkUnder R X ⟶
          CommRingCat.mkUnder R X ⨿ CommRingCat.mkUnder R Y).right := by
  change _ ≫ (CommRingCat.isPushout_tensorProduct R X Y).isoPushout.hom ≫
    (underCoprod_isPushout (CommRingCat.mkUnder R X) (CommRingCat.mkUnder R Y)).isoPushout.inv = _
  rw [← Category.assoc, IsPushout.inl_isoPushout_hom, IsPushout.inl_isoPushout_inv]

private theorem underTensorIso_inr :
    CommRingCat.ofHom (S := X ⊗[R] Y) Algebra.TensorProduct.includeRight.toRingHom ≫
      (underTensorIso R X Y).hom =
        (coprod.inr : CommRingCat.mkUnder R Y ⟶
          CommRingCat.mkUnder R X ⨿ CommRingCat.mkUnder R Y).right := by
  change _ ≫ (CommRingCat.isPushout_tensorProduct R X Y).isoPushout.hom ≫
    (underCoprod_isPushout (CommRingCat.mkUnder R X) (CommRingCat.mkUnder R Y)).isoPushout.inv = _
  rw [← Category.assoc, IsPushout.inr_isoPushout_hom, IsPushout.inr_isoPushout_inv]

end Under

open SerrePositivity.Cosimplicial

variable (k : Type u) [CommRing k] (r : ℕ)

/-- 余積模型の各項を、未完備 pd 模型と通常の多項式環のテンソル積で表す。 -/
def crystallineExtraTermIso (n : SimplexCategory) :
    CommRingCat.of (pdRaw k r n.len ⊗[k] extraVariables k r n.len) ≅
      ((crystallineExtraRaw k r).obj n).right := by
  let X := (pdRawModel k r).obj n
  let E := (extraPolynomialIsoUnder k r).app n
  exact underTensorIso (CommRingCat.of k) (pdRaw k r n.len) (extraVariables k r n.len) ≪≫ (Under.forget (CommRingCat.of k)).mapIso
    (coprod.mapIso (Iso.refl X) E.symm)

private def extraLeft (n : SimplexCategory) :
    ((pdRawModel k r).obj n).right ⟶ ((crystallineExtraRaw k r).obj n).right :=
  (coprod.inl : (pdRawModel k r).obj n ⟶ _).right

private def extraRight (n : SimplexCategory) :
    (extraPolynomial k r).obj n ⟶ (crystallineExtraRaw k r).obj n :=
  polynomialToCechApp k r n ≫ coprod.inr

private theorem extraTermIso_left (n : SimplexCategory) (x : pdRaw k r n.len) :
    (crystallineExtraTermIso k r n).hom (x ⊗ₜ[k] 1) = extraLeft k r n x := by
  let X := (pdRawModel k r).obj n
  let E := (extraPolynomialIsoUnder k r).app n
  let m := coprod.map (𝟙 X) E.inv
  let T := underTensorIso (CommRingCat.of k) (pdRaw k r n.len) (extraVariables k r n.len)
  have h := ConcreteCategory.congr_hom
    (underTensorIso_inl (CommRingCat.of k) (pdRaw k r n.len) (extraVariables k r n.len)) x
  change T.hom (x ⊗ₜ[k] 1) = (coprod.inl : X ⟶ _).right x at h
  change m.right (T.hom (x ⊗ₜ[k] 1)) = _
  have h' := (coprod.inl_map (𝟙 X) E.inv).trans (Category.id_comp _)
  exact (congrArg m.right h).trans (ConcreteCategory.congr_hom
    (congrArg Under.Hom.right h') x)

private theorem extraTermIso_right (n : SimplexCategory) (x : extraVariables k r n.len) :
    (crystallineExtraTermIso k r n).hom (1 ⊗ₜ[k] x) = (extraRight k r n).right x := by
  let X := (pdRawModel k r).obj n
  let Y := (extraPolynomial k r).obj n
  let E := (extraPolynomialIsoUnder k r).app n
  let m := coprod.map (𝟙 X) E.inv
  let T := underTensorIso (CommRingCat.of k) (pdRaw k r n.len) (extraVariables k r n.len)
  have h := ConcreteCategory.congr_hom
    (underTensorIso_inr (CommRingCat.of k) (pdRaw k r n.len) (extraVariables k r n.len)) x
  change T.hom (1 ⊗ₜ[k] x) = (coprod.inr : Y ⟶ _).right x at h
  change m.right (T.hom (1 ⊗ₜ[k] x)) = _
  exact (congrArg m.right h).trans (ConcreteCategory.congr_hom
    (congrArg Under.Hom.right (coprod.inr_map (𝟙 X) E.inv)) x)

private theorem extraLeft_nat {m n : SimplexCategory} (θ : m ⟶ n) :
    extraLeft k r m ≫ ((crystallineExtraRaw k r).map θ).right =
      ((pdRawModel k r).map θ).right ≫ extraLeft k r n :=
  congrArg Under.Hom.right (coprod.inl_map ((pdRawModel k r).map θ)
    ((extraCechUnder k r).map θ))

private theorem extraRight_nat {m n : SimplexCategory} (θ : m ⟶ n) :
    extraRight k r m ≫ (crystallineExtraRaw k r).map θ =
      (extraPolynomial k r).map θ ≫ extraRight k r n := by
  unfold extraRight
  erw [Category.assoc]
  change polynomialToCechApp k r m ≫ (coprod.inr ≫ coprod.map _ _) = _
  erw [coprod.inr_map, ← Category.assoc, ← Category.assoc]
  exact congrArg (fun g => g ≫ coprod.inr) ((extraPolynomialIsoUnder k r).inv.naturality θ).symm

end SerrePositivity.BhattScholze.Prismatic
