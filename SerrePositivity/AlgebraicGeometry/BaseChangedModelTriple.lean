module

public import SerrePositivity.AlgebraicGeometry.BaseChangedModelCartesian
public import SerrePositivity.AlgebraicGeometry.CartesianPullbackComparison

/-!
概要：任意に選んだ構造射のまま、後段の実際の交叉と固定三重交叉の底変換を比較する。
方針：二つの Cartesian 比較を交叉し、係数基底上の正方形へ貼り合わせる。
規約：重なりの構造射は開包含とチャート構造射の合成との可換式で保持する。
使われ方：G2 の六種の式を後段の gluing の式へ戻す。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory Limits
universe u
variable {B S U V W : Scheme.{u}}
  (γ : B ⟶ S) (p : U ⟶ S) (q : V ⟶ S) (r : W ⟶ S)
  (a : V ⟶ U) (c : W ⟶ U) (ha : a ≫ p = q) (hc : c ≫ p = r)

/-- 後段の実際の二つの重なりの交叉から、固定した三重交叉への比較。 -/
def baseChangedModelTripleComparison :
    pullback (baseChangedModelArrow γ q p a ha) (baseChangedModelArrow γ r p c hc) ⟶ pullback a c :=
  cartesianPullbackMap (baseChangedModelArrow γ q p a ha) (baseChangedModelArrow γ r p c hc)
    a c (pullback.snd γ p) (pullback.snd γ q) (pullback.snd γ r)
    (isPullback_baseChangedModelArrow γ q p a ha) (isPullback_baseChangedModelArrow γ r p c hc)

/-- 実際の交叉の比較も同じ基底射の底変換。 -/
theorem isPullback_baseChangedModelTripleComparison :
    IsPullback (baseChangedModelTripleComparison γ p q r a c ha hc)
      (pullback.fst (baseChangedModelArrow γ q p a ha) (baseChangedModelArrow γ r p c hc) ≫
        baseChangedModelArrow γ q p a ha ≫ pullback.fst γ p)
      (pullback.fst a c ≫ a ≫ p) γ := by
  have h := isPullback_cartesianPullbackMap
    (baseChangedModelArrow γ q p a ha) (baseChangedModelArrow γ r p c hc)
    a c (pullback.snd γ p) (pullback.snd γ q) (pullback.snd γ r)
    (isPullback_baseChangedModelArrow γ q p a ha) (isPullback_baseChangedModelArrow γ r p c hc)
  simpa only [baseChangedModelTripleComparison, Category.assoc] using
    h.paste_vert (IsPullback.of_hasPullback γ p).flip

/-- 構造射を保った実際の交叉と固定三重交叉の底変換との具体的な同型。 -/
def baseChangedModelTripleIso :
    pullback (baseChangedModelArrow γ q p a ha) (baseChangedModelArrow γ r p c hc) ≅
      pullback γ (pullback.fst a c ≫ a ≫ p) :=
  (isPullback_baseChangedModelTripleComparison γ p q r a c ha hc).flip.isoPullback

/-- 同型は後段の基底座標を保持する。 -/
@[reassoc (attr := simp)] theorem baseChangedModelTripleIso_hom_fst :
    (baseChangedModelTripleIso γ p q r a c ha hc).hom ≫ pullback.fst γ (pullback.fst a c ≫ a ≫ p) =
      pullback.fst (baseChangedModelArrow γ q p a ha) (baseChangedModelArrow γ r p c hc) ≫
        baseChangedModelArrow γ q p a ha ≫ pullback.fst γ p :=
  (isPullback_baseChangedModelTripleComparison γ p q r a c ha hc).flip.isoPullback_hom_fst

/-- 同型は固定三重交叉への射影を保持する。 -/
@[reassoc (attr := simp)] theorem baseChangedModelTripleIso_hom_snd :
    (baseChangedModelTripleIso γ p q r a c ha hc).hom ≫ pullback.snd γ (pullback.fst a c ≫ a ≫ p) =
      baseChangedModelTripleComparison γ p q r a c ha hc :=
  (isPullback_baseChangedModelTripleComparison γ p q r a c ha hc).flip.isoPullback_hom_snd

end SerrePositivity.AlgebraicGeometry
