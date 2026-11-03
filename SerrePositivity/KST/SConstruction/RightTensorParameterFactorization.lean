module
public import SerrePositivity.KST.SConstruction.DGParameterPullback
public import SerrePositivity.DifferentialGraded.Tensor.Parameter
public import SerrePositivity.DifferentialGraded.Complexes.MaurerCartanCurrying

/-! # 元の右 tensor Hom 写像を通る任意パラメータの因子化
概要：任意 K の右加群 tensor 作用を、既存右加群 Hom と実 tensor Hom の合成で表す。
方針：元の balanced 族の引き戻しと、全加群 Hom の普遍性・currying の自然性を使う。
規約：全次数と元の実 tensor を保つ。使われ方：graph 合成の左入力の tensor 表示。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory Opposite SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- パラメータの引き戻しは、元の右 tensor の balanced 族の引き戻し。 -/
lemma dgRightParamFamily_pullback {K L : Complex A} {M M' : RightModule A D}
    (a : L ⟶ K) (N : LeftModule A D) (τ : ModuleParamTrans A D K M M') :
    BalancedTensor.rightParamFamily A D N (dgParameterPullback A a τ).app
        (dgParameterPullback A a τ).naturality =
      BalancedTensor.paramPrecompose A D M N a
        (BalancedTensor.rightParamFamily A D N τ.app τ.naturality) := by
  apply Subtype.ext
  funext d
  change (α_ L (M.obj (op d)) (N.obj d)).inv ≫
      (uncurryRight (a ≫ τ.app (op d)) ▷ N.obj d) ≫ BalancedTensor.ι A D M' N d =
    (a ▷ (M.obj (op d) ⊗ N.obj d)) ≫ (α_ K (M.obj (op d)) (N.obj d)).inv ≫
      (uncurryRight (τ.app (op d)) ▷ N.obj d) ≫ BalancedTensor.ι A D M' N d
  rw [uncurryRight_precompose, comp_whiskerRight, Category.assoc,
    ← associator_inv_naturality_left_assoc]

/-- 元の右 coend のパラメータ作用は、パラメータの chain map と可換。 -/
lemma dgRightParamMap_pullback {K L : Complex A} {M M' : RightModule A D}
    (a : L ⟶ K) (N : LeftModule A D) (τ : ModuleParamTrans A D K M M') :
    BalancedTensor.rightParamMap A D N (dgParameterPullback A a τ).app
        (dgParameterPullback A a τ).naturality =
      (a ▷ BalancedTensor.obj A D M N) ≫
        BalancedTensor.rightParamMap A D N τ.app τ.naturality := by
  unfold BalancedTensor.rightParamMap
  rw [dgRightParamFamily_pullback, BalancedTensor.paramDesc_precompose]

/-- 任意 K の作用は、元の右加群 Hom 表示と同じ実右 tensor Hom 写像の合成。 -/
lemma dgRightParamHom_factorization {K : Complex A} {M M' : RightModule A D}
    (N : LeftModule A D) (τ : ModuleParamTrans A D K M M') :
    curryRight (BalancedTensor.rightParamMap A D N τ.app τ.naturality) =
      (moduleHomEquiv A D K M M').symm τ ≫ BalancedTensor.rightHomMap A D M M' N := by
  let σ : ModuleParamTrans A D (moduleHom A D M M') M M' :=
    ⟨(fun x => moduleHomπ A D M M' x.unop), moduleHomπ_naturality A D M M'⟩
  let a := (moduleHomEquiv A D K M M').symm τ
  have hf : dgParameterPullback A a σ = τ := by
    apply GradedNatTrans.ext
    funext x
    exact moduleHomEquiv_symm_π A D K M M' τ x.unop
  have h := congrArg (fun υ : ModuleParamTrans A D K M M' =>
    curryRight (BalancedTensor.rightParamMap A D N υ.app υ.naturality)) hf
  rw [dgRightParamMap_pullback] at h
  have hc := curryRight_naturality_source a
    (BalancedTensor.rightParamMap A D N σ.app σ.naturality)
  simp only [tensorHom_id] at hc
  exact h.symm.trans hc

end SerrePositivity.KST.SConstruction
