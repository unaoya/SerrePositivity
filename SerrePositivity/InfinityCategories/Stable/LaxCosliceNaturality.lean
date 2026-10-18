module
public import SerrePositivity.InfinityCategories.Stable.LaxCosliceUniversal

/-! # 太い coslice の普遍性の自然性

概要：太い余錐の curry と uncurry はパラメーターの前合成と可換である。
方針：右直積比較の自然性と普遍性の両逆則を使う。
規約：左図式は固定する。使われ方：coslice の同型類の比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：太い余錐の普遍族はパラメーターの前合成に自然。
方針：右直積比較と fat join の合成則を使う。
規約：左図式の固定条件は不要。使われ方：curry の自然性。 -/
lemma laxCosliceCurryFamily_precomp {A B K X : SSet.{u}}
    (a : A ⟶ B) (F : fatJoin K B ⟶ X) :
    (fatJoin K (Δ[0] : SSet.{u}) ◁ a) ≫ laxCosliceCurryFamily F =
      laxCosliceCurryFamily (fatJoinMap (𝟙 K) a ≫ F) := by
  have he : fatJoinMap (𝟙 K) (Δ[0] ◁ a) ≫ fatJoinMap (𝟙 K) (snd Δ[0] B) =
      fatJoinMap (𝟙 K) (snd Δ[0] A) ≫ fatJoinMap (𝟙 K) a := by
    rw [fatJoinMap_comp, fatJoinMap_comp]
    rfl
  unfold laxCosliceCurryFamily
  rw [← Category.assoc (fatJoin K Δ[0] ◁ a), stableFatJoinTensorRight_naturality]
  simp only [Category.assoc]
  rw [← Category.assoc (fatJoinMap (𝟙 K) (Δ[0] ◁ a)), he]
  simp only [Category.assoc]

/-- 概要：太い coslice の curry は右因子の射に自然。
方針：fiber の包含後に uncurry し、普遍族の自然性を適用する。
規約：左図式を固定する。使われ方：パラメーター付きの比較。 -/
lemma laxCosliceCurry_precomp {A B K X : SSet.{u}} {p : K ⟶ X}
    (a : A ⟶ B) (F : fatJoin K B ⟶ X) (hF : fatJoinInl K B ≫ F = p) :
    laxCosliceCurry (fatJoinMap (𝟙 K) a ≫ F)
      (by rw [← Category.assoc, fatJoinInl_map, Category.id_comp, hF]) =
      a ≫ laxCosliceCurry F hF := by
  apply vertexFiber_hom_ext ((pre (fatJoinInl K (Δ[0] : SSet.{u}))).app X) (functorVertex p)
  change curry (laxCosliceCurryFamily (fatJoinMap (𝟙 K) a ≫ F)) =
    a ≫ curry (laxCosliceCurryFamily F)
  apply uncurry_injective
  rw [uncurry_curry, uncurry_natural_left, uncurry_curry, laxCosliceCurryFamily_precomp]

/-- 概要：太い coslice の uncurry はパラメーターの前合成に自然。
方針：curry の自然性を uncurry して両逆則を使う。
規約：左図式を固定する。使われ方：円柱の両端の比較。 -/
lemma laxCosliceUncurry_precomp {A B K X : SSet.{u}} {p : K ⟶ X}
    (a : A ⟶ B) (f : B ⟶ laxCoslice p) :
    laxCosliceUncurry (a ≫ f) = fatJoinMap (𝟙 K) a ≫ laxCosliceUncurry f := by
  have h := congrArg laxCosliceUncurry
    (laxCosliceCurry_precomp a (laxCosliceUncurry f) (laxCosliceUncurry_fixed f))
  rw [laxCosliceUncurry_curry, laxCosliceCurry_uncurry] at h
  exact h.symm

/-- 概要：太い coslice の射は uncurry した射で決まる。
方針：普遍性の同値の単射性を使う。
規約：左図式は固定する。使われ方：可逆円柱の端点の比較。 -/
lemma laxCosliceUncurry_injective {A K X : SSet.{u}} {p : K ⟶ X} :
    Function.Injective (laxCosliceUncurry (A := A) (p := p)) := by
  intro f g h
  apply (laxCosliceHomEquiv p A).injective
  exact Subtype.ext h

end SerrePositivity.InfinityCategories

