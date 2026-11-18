module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.HomotopicalAlgebra.Complexes.ProjectiveModel
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.CoalgebraInterval

/-!
# 射影モデル構造での単位と区間の端点の cofibrancy

概要：Hovey §2.3、Berger–Moerdijk 命題 4.1 の単位と区間の端点の cofibration 性を証明する。
方針：全射な擬同型に対して sphere の cycle を持ち上げ、直和包含と境界へ合成する。
規約：生成類の持ち上げ性を使い、モデル構造を大域 instance にしない。
使われ方：区間の端点を trivial cofibration として鎖ホモトピー逆を構成する。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.MonoidalCategory _root_.HomologicalComplex
open _root_.SerrePositivity.DifferentialGraded

variable {A : Type u} [CommRing A]

private lemma _root_.SerrePositivity.ProjectiveCofibrantUnit.sphereCycle_comp {K L : Complex A} (n : ℤ)
    (a : complexSphere A n ⟶ K) (f : K ⟶ L) :
    (complexSphereHomEquiv A L n (a ≫ f)).val =
      f.f n (complexSphereHomEquiv A K n a).val := by
  change ((singleObjXSelf (.up ℤ) n (𝟙_ (ModuleCat A))).inv ≫ (a ≫ f).f n) (1 : A) = _
  rw [HomologicalComplex.comp_f]
  rfl

/-- 概要：自由 rank 1 の sphere は射影 cofibrant（Hovey §2.3）。
方針：全射な擬同型の境界持ち上げ条件で零境界の cycle を持ち上げる。
規約：全整数次数に適用する。
使われ方：テンソル単位の cofibrancy を次数零で得る。 -/
lemma _root_.SerrePositivity.ProjectiveCofibrantUnit.projectiveCofibrant_sphere (n : ℤ) :
    (_root_.SerrePositivity.ProjectiveModel.projectiveGeneratingCofibrations A).rlp.llp
      (0 : (HomologicalComplex.zero : Complex A) ⟶ complexSphere A n) := by
  intro K L q hq
  rw [_root_.SerrePositivity.ProjectiveModel.projectiveGeneratingCofibrations_rlp] at hq
  constructor
  intro a b sq
  let z := complexSphereHomEquiv A L n b
  obtain ⟨t, ht, hqt⟩ := complex_boundary_lifting_of_surjective_quasiIso A q hq.1 hq.2 n
    ⟨0, by simp⟩ z.val (by rw [map_zero]; exact z.property.symm)
  apply CommSq.HasLift.mk'
  refine { l := (complexSphereHomEquiv A K n).symm ⟨t, ht⟩
           fac_left := HomologicalComplex.isZero_zero.eq_of_src _ _
           fac_right := ?_ }
  apply (complexSphereHomEquiv A L n).injective
  apply Subtype.ext
  rw [_root_.SerrePositivity.ProjectiveCofibrantUnit.sphereCycle_comp, Equiv.apply_symm_apply]
  exact hqt

/-- 概要：テンソル単位は射影 cofibrant（Hovey §2.3）。
方針：単位が次数零の sphere である定義を使う。
規約：基礎環は任意の可換環。
使われ方：区間の境界の各端点包含を cofibration とする。 -/
lemma _root_.SerrePositivity.ProjectiveCofibrantUnit.projectiveCofibrant_unit :
    (_root_.SerrePositivity.ProjectiveModel.projectiveGeneratingCofibrations A).rlp.llp
      (0 : (HomologicalComplex.zero : Complex A) ⟶ 𝟙_ (Complex A)) := by
  exact _root_.SerrePositivity.ProjectiveCofibrantUnit.projectiveCofibrant_sphere 0

/-- 概要：cofibrant な右因子を加える左直和包含は cofibration（Hovey §2.3）。
方針：右因子からの射を持ち上げて左因子からの指定した射と直和にする。
規約：左因子に cofibrancy を要求しない。
使われ方：単位二点の片側からの包含を区間の境界へ合成する。 -/
lemma _root_.SerrePositivity.ProjectiveCofibrantUnit.projectiveCofibration_biprod_inl (X Y : Complex A)
    (hY : (_root_.SerrePositivity.ProjectiveModel.projectiveGeneratingCofibrations A).rlp.llp
      (0 : (HomologicalComplex.zero : Complex A) ⟶ Y)) :
    (_root_.SerrePositivity.ProjectiveModel.projectiveGeneratingCofibrations A).rlp.llp (biprod.inl : X ⟶ X ⊞ Y) := by
  intro K L q hq
  constructor
  intro a b sq
  let s : CommSq (0 : (HomologicalComplex.zero : Complex A) ⟶ K) 0 q
      ((biprod.inr : Y ⟶ X ⊞ Y) ≫ b) := ⟨by simp⟩
  obtain ⟨l⟩ := ((hY q hq).sq_hasLift s).exists_lift
  apply CommSq.HasLift.mk'
  refine { l := biprod.desc a l.l
           fac_left := by simp
           fac_right := ?_ }
  apply biprod.hom_ext'
  · simpa only [Category.assoc, biprod.inl_desc_assoc] using sq.w
  · simpa only [Category.assoc, biprod.inr_desc_assoc] using l.fac_right

namespace InfinityCategories.Models.EInfinity.DGOperads.Operad.CoalgebraInterval

variable {P : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A} {ε : P ⟶ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.commutativeOperad A}

/-- 概要：区間の始点は射影 cofibration（BM 命題 4.1）。
方針：単位二点の左包含と指定した境界 cofibration を合成する。
規約：区間に追加の cofibrancy を仮定しない。
使われ方：既存の端点の擬同型性と合わせて trivial cofibration を得る。 -/
lemma _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.CoalgebraInterval.endpoint_false_cofibration (I : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.CoalgebraInterval ε) :
    (_root_.SerrePositivity.ProjectiveModel.projectiveGeneratingCofibrations A).rlp.llp (I.endpoint false) := by
  have h := (_root_.SerrePositivity.ProjectiveModel.projectiveGeneratingCofibrations A).rlp.llp.comp_mem
    (biprod.inl : (𝟙_ (Complex A)) ⟶ (𝟙_ (Complex A)) ⊞ (𝟙_ (Complex A))) I.boundary
    (_root_.SerrePositivity.ProjectiveCofibrantUnit.projectiveCofibration_biprod_inl _ _ _root_.SerrePositivity.ProjectiveCofibrantUnit.projectiveCofibrant_unit) I.boundary_cofibration
  simpa only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.CoalgebraInterval.boundary, biprod.inl_desc] using h

end InfinityCategories.Models.EInfinity.DGOperads.Operad.CoalgebraInterval

end SerrePositivity

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HA "7.1.2.11" (partial := component) "仮定：任意可換環 R の非有界複体と構成済み射影モデル構造（HA と一致）。結論：テンソル単位の cofibrancy と任意 cofibrant X による左テンソルの左 Quillen 性を示す（HA のモノイダル模型の結論の一部に一致）。任意の二つの cofibration の pushout-product 公理全体を登録した宣言は含まれない。"] _root_.SerrePositivity.ProjectiveCofibrantUnit.projectiveCofibrant_unit
