module

public import SerrePositivity.InfinityCategories.F2.Ind.ConePointSliceLiftTip
public import SerrePositivity.InfinityCategories.F2.Ind.ConeTerminalSliceLiftNaturality
public import SerrePositivity.InfinityCategories.F2.Ind.ConeTerminalSliceComparison
public import SerrePositivity.InfinityCategories.F2.Ind.RightAnodyneRelativeLiftNaturality

/-!
概要：任意の元の点写像に対する全余錐の比較を、同じ全底と恒等終点を固定して構成する。
方針：元の点の標準持ち上げと同じ right-anodyne 制限の指定逆像を使う。
規約：元の点と全底図式を保持し、元の比較の前合成の指定値を回収する。
使われ方：元の極大点評価の指定変換を旧族で保持する相対余錐。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
variable {A X : SSet.{u}} [Quasicategory X] (p : (Δ[0] : SSet.{u}) ⟶ X)
  (b : join A (Δ[0] : SSet.{u}) ⟶ X) (hb : joinInr A Δ[0] ≫ b = p)
  (W : join A (Δ[0] : SSet.{u}) ⟶ sliceOver p) (hp : W ≫ sliceOverProjection p = b)
  (ht : sliceOverUncurry (joinInr A Δ[0] ≫ W) = SSet.const (SSet.yonedaEquiv p))
/-- 概要：元の同じ点と全底上で、恒等終点を固定した指定比較。
方針：同じ right-anodyne 制限の逆像。規約：全射を保持。使われ方：指定変換の保持。 -/
def conePointSliceRelativeIso :
    VertexIso (relativeFunctorVertex (sliceOverProjection p) b W hp)
      (relativeFunctorVertex (sliceOverProjection p) b (conePointSliceLift p b hb)
        (conePointSliceLift_projection p b hb)) :=
  rightAnodyneRelativeLiftIso (sliceOverProjection p) b (joinInr A Δ[0])
    (coneTip_rightAnodyne A) W (conePointSliceLift p b hb) hp
    (conePointSliceLift_projection p b hb) (by
      apply sliceOverUncurry_injective p
      rw [ht, conePointSliceLift_tip_uncurry])
/-- 概要：任意の元の点の全余錐比較は、旧族で同じ元の比較へ制限される。
方針：同じ指定逆像と標準持ち上げの自然性。規約：同じ指定値。使われ方：旧族の変換保持。 -/
lemma conePointSliceRelativeIso_precomp {A₀ : SSet.{u}} (k : A₀ ⟶ A) : HEq
    (VertexIso.map (conePointSliceRelativeIso p b hb W hp ht)
      (relativeFunctorPre (sliceOverProjection p) b (joinMap k (𝟙 Δ[0]))))
    (conePointSliceRelativeIso p (joinMap k (𝟙 Δ[0]) ≫ b)
      (by rw [← Category.assoc, joinInr_joinMap, Category.id_comp]; exact hb)
      (joinMap k (𝟙 Δ[0]) ≫ W) (by rw [Category.assoc, hp]) (by
        rw [← Category.assoc, joinInr_joinMap, Category.id_comp]
        exact ht)) := by
  have hn := rightAnodyneRelativeLiftIso_precomp (p := sliceOverProjection p) (b := b)
    (f := W) (g := conePointSliceLift p b hb) (hf := hp)
    (hg := conePointSliceLift_projection p b hb)
    (j := joinMap k (𝟙 Δ[0])) (i₀ := joinInr A₀ (Δ[0] : SSet.{u}))
    (hi₀ := coneTip_rightAnodyne A₀)
    (hij := by rw [joinInr_joinMap, Category.id_comp]; exact coneTip_rightAnodyne A)
    (hh := by
      apply sliceOverUncurry_injective p
      rw [joinInr_joinMap, Category.id_comp, ht, conePointSliceLift_tip_uncurry])
  have h := heq_of_eq hn
  simp only [joinInr_joinMap, Category.id_comp, conePointSliceRelativeIso] at h ⊢
  refine h.trans ?_
  apply rightAnodyneRelativeLiftIso_heq
  · rfl
  · exact conePointSliceLift_precomp p b hb k
end SerrePositivity.InfinityCategories.F2.Ind
