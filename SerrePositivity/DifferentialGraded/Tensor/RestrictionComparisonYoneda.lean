module
public import SerrePositivity.DifferentialGraded.Tensor.RestrictionComparison
public import SerrePositivity.DifferentialGraded.Tensor.Yoneda
public import SerrePositivity.DifferentialGraded.Tensor.LeftKFlatResolution
public import SerrePositivity.DifferentialGraded.Module.RestrictionRepresentable

/-! # 制限tensor比較と代表加群のYoneda評価

## 概要
Hom準同型性と制限後の左相対K-flat性の下で、像の代表加群における比較を検証する。

## 方針
balanced tensor・全Hom自然性・作用の既存計算と普遍性を使い、条件を明示して比較する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。局所導来合成の計算部品、一般Morita・相対tensor・Hochschild型構成での作用と符号の比較に使える。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded.BalancedTensor
open CategoryTheory MonoidalCategory Opposite HomologicalComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E] (F : DGFunctor A D E)

/-- Hom写像による代表加群比較を制限された左因子とtensorする。 -/
def representableRestrictionTensorMap (d : D) (N : LeftModule A E) :
    obj A D (representable A d) (F.comp N) ⟶
      obj A D (restrictModule A D E F.op (representable A (F.obj d))) (F.comp N) :=
  (rightTensorFunctor A D (F.comp N)).map (representableRestrictionMap A D E F d)

@[reassoc (attr := simp)]
lemma ι_representableRestrictionTensorMap (d x : D) (N : LeftModule A E) :
    ι A D (representable A d) (F.comp N) x ≫
        representableRestrictionTensorMap A D E F d N =
      (F.map x d ⊗ₘ 𝟙 (N.obj (F.obj x))) ≫
        ι A D (restrictModule A D E F.op (representable A (F.obj d))) (F.comp N) x := by
  have h := ι_map A D (representableRestrictionMap A D E F d)
    (𝟙 (ForgetEnrichment.of (Complex A) (F.comp N))) x
  rw [representableRestrictionMap_eval, CategoryTheory.Functor.map_id] at h
  exact h

/-- 比較と代表加群のHom写像を合わせると、元のYoneda評価そのものになる。 -/
lemma representableRestrictionTensorMap_comparison_yoneda (d : D) (N : LeftModule A E) :
    representableRestrictionTensorMap A D E F d N ≫
        restrictionComparison A D E F (representable A (F.obj d)) N ≫
          yonedaEvaluation A E (F.obj d) N = yonedaEvaluation A D d (F.comp N) := by
  apply hom_ext
  intro x
  rw [ι_representableRestrictionTensorMap_assoc, ι_restrictionComparison_assoc,
    ι_yonedaEvaluation, ι_yonedaEvaluation]
  exact (leftAction_restrict A D E F N x d).symm

lemma representableRestrictionTensorMap_quasiIso (hF : HomQuasiIso F) (d : D)
    (N : LeftModule A E) (hN : leftModuleRelativeKFlat A D (F.comp N)) :
    QuasiIso (representableRestrictionTensorMap A D E F d N) :=
  leftModuleRelativeKFlat_preserves_rightQuasiIso A D (F.comp N) hN
    (representableRestrictionMap A D E F d) (representableRestrictionMap_quasiIso A D E F hF d)

/-- 像の代表加群における実際の比較chain mapの準同型性。 -/
lemma restrictionComparison_representable_quasiIso (hF : HomQuasiIso F) (d : D)
    (N : LeftModule A E) (hN : leftModuleRelativeKFlat A D (F.comp N)) :
    QuasiIso (restrictionComparison A D E F (representable A (F.obj d)) N) := by
  have : QuasiIso (representableRestrictionTensorMap A D E F d N) :=
    representableRestrictionTensorMap_quasiIso A D E F hF d N hN
  have : IsIso (yonedaEvaluation A E (F.obj d) N) := (yonedaIso A E (F.obj d) N).isIso_hom
  have : IsIso (yonedaEvaluation A D d (F.comp N)) := (yonedaIso A D d (F.comp N)).isIso_hom
  have : QuasiIso (representableRestrictionTensorMap A D E F d N ≫
      restrictionComparison A D E F (representable A (F.obj d)) N ≫
        yonedaEvaluation A E (F.obj d) N) := by
    rw [representableRestrictionTensorMap_comparison_yoneda]
    infer_instance
  have : QuasiIso (restrictionComparison A D E F (representable A (F.obj d)) N ≫
      yonedaEvaluation A E (F.obj d) N) :=
    quasiIso_of_comp_left (representableRestrictionTensorMap A D E F d N) _
  exact quasiIso_of_comp_right _ (yonedaEvaluation A E (F.obj d) N)

end SerrePositivity.DifferentialGraded.BalancedTensor
