module
public import SerrePositivity.DifferentialGraded.Module.LeftClosedMaps

/-! # 左dg加群の閉零射の全Hom自然性をchain mapの式で読む

## 概要
左dg加群の閉零射の全Hom自然性をchain mapの式で読む。

## 方針
既存の全dg自然なHom・作用・chain mapと局所化の計算を再利用する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanの依存。直接の利用箇所：Bimodule/TensorModuleMaps.lean。dg加群の導来作用・準同値比較の基盤。
任意可換環上のMorita・K理論のモデル比較に再利用できる。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Opposite
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

lemma leftModuleMorphism_naturality {M N : LeftModuleCategory A D} (f : M ⟶ N) (x y : D) :
    (ForgetEnrichment.to (Complex A) M).map x y ≫
      homPostcompose ((ForgetEnrichment.to (Complex A) M).obj x)
        ((leftModuleEvaluation A D y).map f) =
    (ForgetEnrichment.to (Complex A) N).map x y ≫
      homPrecompose ((leftModuleEvaluation A D x).map f)
        ((ForgetEnrichment.to (Complex A) N).obj y) := by
  have h := closedTransApp_naturality A (leftModuleClosedHomEquiv A D M N f)
    (op (op x)) (op (op y))
  change (𝟙 _ ≫ (ForgetEnrichment.to (Complex A) M).map x y) ≫
      homPostcompose ((ForgetEnrichment.to (Complex A) M).obj x)
        ((leftModuleEvaluation A D y).map f) =
    (𝟙 _ ≫ (ForgetEnrichment.to (Complex A) N).map x y) ≫
      homPrecompose ((leftModuleEvaluation A D x).map f)
        ((ForgetEnrichment.to (Complex A) N).obj y) at h
  simpa only [Category.id_comp] using h

end SerrePositivity.DifferentialGraded
