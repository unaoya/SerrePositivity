module

public meta import SerrePositivity.Util.DeprecatedAlias
public import SerrePositivity.AlgebraicGeometry.TensorPureTransformBaseChange
public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction

/-!
概要：KST §5、Stacks 0815 の純変換の平坦性をアフィン試験対象への引き戻しで表す。
方針：Spec の充満忠実性で係数写像を取り、実際の加群の平坦性を量化する。
規約：正則な境界を持つ試験対象を使い、平坦化中心の存在を仮定フィールドに置かない。
使われ方：構成済みの局所中心を共通細分と開被覆でまとめる。
-/

@[expose] public noncomputable section
universe u v
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory
open scoped TensorProduct

/--
概要：スキーム射へのアフィン試験射から得られる基礎環の係数写像。
方針：Spec 間の合成射を環準同型へ戻す。
規約：KST §5、Stacks 0815、写像の向きは基礎環から試験対象の環。
使われ方：純変換の引き戻しの係数環を固定する。
-/
def pureTransformCoefficientMap {R A : CommRingCat.{u}} {X : Scheme.{u}}
    (p : X ⟶ Spec R) (j : Spec A ⟶ X) : R →+* A := (Spec.preimage (j ≫ p)).hom

/--
概要：正則な境界を持つ全アフィン試験対象で純変換が平坦となる性質。
方針：各係数写像に対する実際のテンソル積の純変換の平坦性を要求する。
規約：KST §5、Stacks 0815、中心の存在定理や引用をこの定義に含めない。
使われ方：Noether アフィンモデルから証明し、開被覆で貼り合わせる。
-/
def HasFlatPurePullbacks {R : CommRingCat.{u}} {X : Scheme.{u}}
    (p : X ⟶ Spec R) (f : R) (M : Type v) [AddCommGroup M] [Module R M] : Prop :=
  ∀ (A : CommRingCat.{u}) (j : Spec A ⟶ X),
    let φ := pureTransformCoefficientMap p j
    letI : Algebra R A := φ.toAlgebra
    IsRegular (φ f) → Module.Flat A (modulePureTransform (φ f) (A ⊗[R] M))

/--
概要：アフィン試験対象の係数写像はスキーム射の合成の括弧の変更で変わらない。
方針：圏の合成の結合則を使う。
規約：KST §5、Stacks 0815、係数環の準同型の等式。
使われ方：引き戻し平坦性の合成に関する安定性。
-/
theorem pureTransformCoefficientMap_comp {R A : CommRingCat.{u}} {X Y : Scheme.{u}}
    (p : X ⟶ Spec R) (q : Y ⟶ X) (j : Spec A ⟶ Y) :
    pureTransformCoefficientMap (q ≫ p) j = pureTransformCoefficientMap p (j ≫ q) := by
  simp only [pureTransformCoefficientMap, Category.assoc]

/--
概要：アフィン試験対象での純変換の平坦性は任意の前合成で保たれる。
方針：試験射に前合成する射を合成して元の性質を適用する。
規約：KST §5、Stacks 0815、正則性は同じ係数写像で判定する。
使われ方：共通細分から局所平坦化した blowup への射に適用する。
-/
theorem HasFlatPurePullbacks.comp {R : CommRingCat.{u}} {X Y : Scheme.{u}}
    {p : X ⟶ Spec R} {f : R} {M : Type v} [AddCommGroup M] [Module R M]
    (hp : HasFlatPurePullbacks p f M) (q : Y ⟶ X) : HasFlatPurePullbacks (q ≫ p) f M := by
  intro A j
  let P (φ : R →+* A) : Prop :=
    letI : Algebra R A := φ.toAlgebra
    IsRegular (φ f) → Module.Flat A (modulePureTransform (φ f) (A ⊗[R] M))
  exact (congrArg P (pureTransformCoefficientMap_comp p q j)).mpr (hp A (j ≫ q))

/--
概要：Spec 間の射を経た係数写像は環準同型の合成である。
方針：Spec の逆写像が反変の合成を保つことを使う。
規約：KST §5、Stacks 0815、環の射は CommRingCat の射で指定する。
使われ方：環論上の追加基底変更をスキーム上の性質へ接続する。
-/
theorem pureTransformCoefficientMap_spec {R A B : CommRingCat.{u}}
    (φ : R ⟶ A) (j : Spec B ⟶ Spec A) :
    pureTransformCoefficientMap (Spec.map φ) j = (Spec.preimage j).hom.comp φ.hom := by
  unfold pureTransformCoefficientMap
  rw [Spec.preimage_comp, Spec.preimage_map]
  rfl

/--
概要：アフィン試験射の可換な因子化では係数写像も対応する環準同型の合成となる。
方針：スキーム射の交換式を Spec の逆写像で環の交換式へ戻す。
規約：KST §5、Stacks 0815、θ は試験対象の係数拡大の射。
使われ方：基本開上の持ち上げによる純変換の係数の照合。
-/
theorem pureTransformCoefficientMap_factor {R A B : CommRingCat.{u}}
    {X Y : Scheme.{u}} (p : X ⟶ Spec R) (q : Y ⟶ X) (j : Spec A ⟶ X)
    (g : Spec B ⟶ Y) (θ : A ⟶ B) (h : g ≫ q = Spec.map θ ≫ j) :
    pureTransformCoefficientMap (q ≫ p) g = θ.hom.comp (pureTransformCoefficientMap p j) := by
  have heq : g ≫ (q ≫ p) = Spec.map θ ≫ (j ≫ p) := by
    rw [← Category.assoc, h, Category.assoc]
  unfold pureTransformCoefficientMap
  rw [heq, Spec.preimage_comp, Spec.preimage_map]
  rfl

/--
概要：基礎環の Spec への後合成に対する係数写像の公式。
方針：Spec の逆写像の反変合成を使う。
規約：KST §5、Stacks 0815、φ は元の基礎環から中間環への射。
使われ方：チャート環上の平坦性を元の基礎環について表す。
-/
theorem pureTransformCoefficientMap_post_spec {R A B : CommRingCat.{u}}
    {X : Scheme.{u}} (p : X ⟶ Spec A) (φ : R ⟶ A) (j : Spec B ⟶ X) :
    pureTransformCoefficientMap (p ≫ Spec.map φ) j =
      (pureTransformCoefficientMap p j).comp φ.hom := by
  unfold pureTransformCoefficientMap
  rw [← Category.assoc, Spec.preimage_comp, Spec.preimage_map]
  rfl

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
