module

public import SerrePositivity.AlgebraicGeometry.AtlasGluingMap
public import SerrePositivity.AlgebraicGeometry.FinitePresentationGluingBase

/-!
概要：各チャートの Cartesian な係数比較を、貼り合わせた対象全体へ渡す。
方針：元の開と模型のチャートの正方形を使い、模型の開被覆上で pullback を判定する。
規約：貼り合わせの比較の法則。模型の存在の入力を隠さない。
使われ方：G2 の一般の有限表示対象の実際の底変換比較。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory Limits
universe u

/-- 各チャートの係数比較が Cartesian なら、貼り合わせた対象全体の係数比較も Cartesian。 -/
theorem isPullback_gluingAtlasMap_toBase
    (D : Scheme.GlueData.{u}) {X S T : Scheme.{u}}
    (U : D.J → Scheme.{u}) (j : ∀ i, U i ⟶ X) [∀ i, IsOpenImmersion (j i)]
    (hcover : ∀ x : X, ∃ i z, j i z = x)
    (a : ∀ i, U i ⟶ D.U i)
    (b : ∀ i k, pullback (j i) (j k) ⟶ D.V (i, k))
    (hb : ∀ i k, IsPullback (b i k) (pullback.fst (j i) (j k)) (D.f i k) (a i))
    (hcompat : ∀ i k, b i k ≫ D.t i k ≫ D.f k i = pullback.snd (j i) (j k) ≫ a k)
    (p : ∀ i, D.U i ⟶ S)
    (hp : ∀ i k, D.f i k ≫ p i = D.t i k ≫ D.f k i ≫ p k)
    (f : X ⟶ T) (g : T ⟶ S)
    (hchart : ∀ i, IsPullback (a i) (j i ≫ f) (p i) g) :
    IsPullback (gluingAtlasMap D U j hcover a b hb hcompat) f (glueDataToBase D p hp) g := by
  let F := gluingAtlasMap D U j hcover a b hb hcompat
  apply Scheme.isPullback_of_openCover F f (glueDataToBase D p hp) g D.openCover
  intro i
  change IsPullback (pullback.snd F (D.ι i)) (pullback.fst F (D.ι i) ≫ f)
    (D.ι i ≫ glueDataToBase D p hp) g
  rw [glueDataToBase_ι]
  let hc := isPullback_gluingAtlasMap_chart D U j hcover a b hb hcompat i
  let e := hc.flip.isoPullback
  refine (hchart i).of_iso e (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  · change a i = hc.flip.isoPullback.hom ≫ pullback.snd _ _
    exact hc.flip.isoPullback_hom_snd.symm
  · change j i ≫ f = hc.flip.isoPullback.hom ≫ pullback.fst _ _ ≫ f
    exact (hc.flip.isoPullback_hom_fst_assoc f).symm
  · simp
  · simp

end SerrePositivity.AlgebraicGeometry
