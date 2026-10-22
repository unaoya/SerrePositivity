module

public import SerrePositivity.InfinityCategories.F1.ConeParameterPrism
public import SerrePositivity.InfinityCategories.F1.SliceConeFamilyEndpoints

/-!
概要：頂点が動く元の native な錐の全族を、同じ内部 Hom 表示の円柱で評価する。
方針：既存の slice からの普遍族を使い、両端とパラメータ自然性を計算する。
規約：元の Hom 比較と native な錐の表示を保持する。
使われ方：right Hom の輸送円柱による合成の正方形。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories
open HomotopyLimits
variable {K X T U : SSet.{u}} {f : K ⟶ X}

/-- 元の可変頂点の錐の全族を同じ円柱の順で評価する。 -/
def coneVariablePrism (a : T ⟶ sliceOver f) : (K ⊗ (Δ[1] : SSet.{u})) ⊗ T ⟶ X :=
  (coneCylinderMap K ▷ T) ≫ (join (Δ[0] : SSet.{u}) K ◁ a) ≫ sliceConeFamilyUncurry f

/-- 円柱の始点は元の可変頂点の射影。 -/
lemma coneVariablePrism_zero (a : T ⟶ sliceOver f) :
    (SSet.ι₀ ▷ T) ≫ coneVariablePrism a = snd K T ≫ a ≫ sliceOverProjection f := by
  rw [coneVariablePrism, ← Category.assoc, ← comp_whiskerRight, coneCylinderMap_zero,
    comp_whiskerRight, Category.assoc, ← Category.assoc (joinInl Δ[0] K ▷ T),
    ← whisker_exchange, Category.assoc, sliceConeFamilyUncurry_inl,
    whiskerLeft_snd_assoc, whiskerRight_snd_assoc]

/-- 円柱の終点は同じ元の固定図式。 -/
lemma coneVariablePrism_one (a : T ⟶ sliceOver f) :
    (SSet.ι₁ ▷ T) ≫ coneVariablePrism a = fst K T ≫ f := by
  rw [coneVariablePrism, ← Category.assoc, ← comp_whiskerRight, coneCylinderMap_one,
    ← Category.assoc, ← whisker_exchange, Category.assoc, sliceConeFamilyUncurry_fixed,
    whiskerLeft_fst_assoc]

/-- 頂点が動く円柱も、任意の部分族への制限と厳密に可換。 -/
lemma coneVariablePrism_precomp (i : T ⟶ U) (a : U ⟶ sliceOver f) :
    coneVariablePrism (i ≫ a) = ((K ⊗ (Δ[1] : SSet.{u})) ◁ i) ≫ coneVariablePrism a := by
  dsimp only [coneVariablePrism]
  rw [whiskerLeft_comp]
  simpa only [Category.assoc] using congrArg
    (fun k ↦ k ≫ (join (Δ[0] : SSet.{u}) K ◁ a) ≫ sliceConeFamilyUncurry f)
    (whisker_exchange (coneCylinderMap K) i).symm

/-- 同じ可変頂点の円柱は、元の slice の比較の内部 Hom の全評価である。 -/
lemma coneVariablePrism_uncurry (a : T ⟶ sliceOver f) :
    coneVariablePrism a = (coneCylinderMap K ▷ T) ≫
      uncurry (a ≫ sliceConeFamilyMap f ≫ vertexFiberι (coneRestriction K X) (functorVertex f)) := by
  rw [sliceConeFamilyMap, vertexFiberLift_ι, uncurry_natural_left,
    uncurry_curry]
  rfl

/-- 頂点を固定した場合も、同じ native な比較の全円柱そのものを回収する。 -/
lemma coneVariablePrism_fixed {z : X _⦋0⦌} (a : T ⟶ vertexFiber (sliceOverProjection f) z) :
    coneVariablePrism (a ≫ vertexFiberι (sliceOverProjection f) z) =
      coneParameterPrism (a ≫ coneVertexFiberFamilyMap f z) := by
  rw [coneVariablePrism_uncurry, coneParameterPrism]
  rfl

end SerrePositivity.InfinityCategories
