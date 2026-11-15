module

public import SerrePositivity.AlgebraicGeometry.BaseChangedOverlapMap
public import SerrePositivity.AlgebraicGeometry.CartesianPullbackComparison

/-!
概要：実際の段の重なりの交叉と、固定した三重交叉模型の底変換を具体的に同一視する。
方針：二つの Cartesian な開の比較を交叉し、係数基底上の Cartesian 正方形へ貼り合わせる。
規約：段の基底射は任意。開包含の仮定すら同型の構成には不要。
使われ方：G2 の降ろした三重交叉の射を gluing datum の実際の三重交叉へ移す。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory Limits
universe u
variable {B S U V W : Scheme.{u}}
  (γ : B ⟶ S) (p : U ⟶ S) (q : V ⟶ U) (r : W ⟶ U)

/-- 段の二つの重なりの交叉から固定した三重交叉への実際の比較。 -/
def baseChangedOverlapTripleComparison :
    pullback (baseChangedOverlapMap γ p q) (baseChangedOverlapMap γ p r) ⟶ pullback q r :=
  cartesianPullbackMap (baseChangedOverlapMap γ p q) (baseChangedOverlapMap γ p r)
    q r (pullback.snd γ p) (pullback.snd γ (q ≫ p)) (pullback.snd γ (r ≫ p))
    (isPullback_baseChangedOverlapMap γ p q) (isPullback_baseChangedOverlapMap γ p r)

/-- 交叉の比較も同じ係数基底の底変換。 -/
theorem isPullback_baseChangedOverlapTripleComparison :
    IsPullback (baseChangedOverlapTripleComparison γ p q r)
      (pullback.fst (baseChangedOverlapMap γ p q) (baseChangedOverlapMap γ p r) ≫
        baseChangedOverlapMap γ p q ≫ pullback.fst γ p)
      (pullback.fst q r ≫ q ≫ p) γ := by
  have h := isPullback_cartesianPullbackMap
    (baseChangedOverlapMap γ p q) (baseChangedOverlapMap γ p r)
    q r (pullback.snd γ p) (pullback.snd γ (q ≫ p)) (pullback.snd γ (r ≫ p))
    (isPullback_baseChangedOverlapMap γ p q) (isPullback_baseChangedOverlapMap γ p r)
  simpa only [baseChangedOverlapTripleComparison, Category.assoc] using h.paste_vert (IsPullback.of_hasPullback γ p).flip

/-- 段の実際の三重交叉と固定した三重交叉模型の底変換との具体的な同型。 -/
def baseChangedOverlapTripleIso :
    pullback (baseChangedOverlapMap γ p q) (baseChangedOverlapMap γ p r) ≅
      pullback γ (pullback.fst q r ≫ q ≫ p) :=
  (isPullback_baseChangedOverlapTripleComparison γ p q r).flip.isoPullback

/-- 同型は段の基底座標を保つ。 -/
@[reassoc (attr := simp)] theorem baseChangedOverlapTripleIso_hom_fst :
    (baseChangedOverlapTripleIso γ p q r).hom ≫ pullback.fst γ (pullback.fst q r ≫ q ≫ p) =
      pullback.fst (baseChangedOverlapMap γ p q) (baseChangedOverlapMap γ p r) ≫
        baseChangedOverlapMap γ p q ≫ pullback.fst γ p :=
  (isPullback_baseChangedOverlapTripleComparison γ p q r).flip.isoPullback_hom_fst

/-- 同型は固定した三重交叉への実際の射影を保つ。 -/
@[reassoc (attr := simp)] theorem baseChangedOverlapTripleIso_hom_snd :
    (baseChangedOverlapTripleIso γ p q r).hom ≫ pullback.snd γ (pullback.fst q r ≫ q ≫ p) =
      baseChangedOverlapTripleComparison γ p q r :=
  (isPullback_baseChangedOverlapTripleComparison γ p q r).flip.isoPullback_hom_snd

end SerrePositivity.AlgebraicGeometry
