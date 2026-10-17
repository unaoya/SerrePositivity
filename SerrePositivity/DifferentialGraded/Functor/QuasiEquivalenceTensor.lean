module
public import SerrePositivity.DifferentialGraded.Functor.Tensor
public import SerrePositivity.DifferentialGraded.Functor.QuasiEquivalence
public import SerrePositivity.DifferentialGraded.Category.TensorInclusions
public import SerrePositivity.DifferentialGraded.Tensor.ObjectwiseKFlat
public import SerrePositivity.DifferentialGraded.Tensor.KFlatComplex

/-! # 局所K-flat性を明示したtensor積dg関手の準同値保存

## 概要
局所K-flat性を明示したtensor積dg関手の準同値保存。

## 方針
既存の全dg自然なHom・作用・chain mapと局所化の計算を再利用する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。dg加群の導来作用・準同値比較の基盤。任意可換環上のMorita・K理論のモデル比較に再利用できる。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z t
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory HomologicalComplex
variable {A : Type u} [CommRing A] {B : Type v} {C : Type w} {D : Type z} {E : Type t}
  [DGCategory A B] [DGCategory A C] [DGCategory A D] [DGCategory A E]
  (F : DGFunctor A B D) (G : DGFunctor A C E)

/-- まずF、次にGのHom写像をtensorする。相手のK-flat性はCとDに要求する。 -/
lemma homQuasiIso_tensor (hF : HomQuasiIso F) (hG : HomQuasiIso G)
    (hC : localHomKFlat A C) (hD : localHomKFlat A D) : HomQuasiIso (F.tensor G) := by
  intro x y
  have := hF x.1 y.1
  have := hG x.2 y.2
  have h₁ := complexKFlat_quasiIso_left A (hC x.2 y.2) (F.map x.1 y.1)
  have h₂ := complexKFlat_quasiIso_right A (hD (F.obj x.1) (F.obj y.1)) (G.map x.2 y.2)
  let := h₁
  let := h₂
  change QuasiIso (F.map x.1 y.1 ⊗ₘ G.map x.2 y.2)
  have hi : QuasiIso ((F.map x.1 y.1 ⊗ₘ 𝟙 (x.2 ⟶[Complex A] y.2)) ≫
      (𝟙 (F.obj x.1 ⟶[Complex A] F.obj y.1) ⊗ₘ G.map x.2 y.2)) := by infer_instance
  simpa only [tensorHom_comp_tensorHom, Category.comp_id, Category.id_comp] using hi

/-- 本質的全射性のtensor保存自体にはflatnessを使わない。 -/
lemma DGFunctor.onHomotopy_tensor_essSurj (hF : F.onHomotopy.EssSurj)
    (hG : G.onHomotopy.EssSurj) : (F.tensor G).onHomotopy.EssSurj where
  mem_essImage y := by
    let := hF
    let := hG
    let e := ForgetEnrichment.to (Complex A) y.as
    let Y₁ := (toHomotopy A D).obj (ForgetEnrichment.of (Complex A) e.1)
    let Y₂ := (toHomotopy A E).obj (ForgetEnrichment.of (Complex A) e.2)
    let X₁ := F.onHomotopy.objPreimage Y₁
    let X₂ := G.onHomotopy.objPreimage Y₂
    let b := ForgetEnrichment.to (Complex A) X₁.as
    let c := ForgetEnrichment.to (Complex A) X₂.as
    let i₁ := F.onHomotopy.objObjPreimageIso Y₁
    let i₂ := G.onHomotopy.objObjPreimageIso Y₂
    refine ⟨(toHomotopy A (DGTensorCategory A B C)).obj
      (ForgetEnrichment.of (Complex A) ((b, c) : DGTensorCategory A B C)), ⟨?_⟩⟩
    exact ((dgTensorIncludeFirst A D E (G.obj c)).onHomotopy.mapIso i₁) ≪≫
      ((dgTensorIncludeSecond A D E e.1).onHomotopy.mapIso i₂)

lemma quasiEquivalence_tensor (hF : QuasiEquivalence F) (hG : QuasiEquivalence G)
    (hC : localHomKFlat A C) (hD : localHomKFlat A D) : QuasiEquivalence (F.tensor G) :=
  ⟨homQuasiIso_tensor F G hF.1 hG.1 hC hD, F.onHomotopy_tensor_essSurj G hF.2 hG.2⟩

end SerrePositivity.DifferentialGraded
