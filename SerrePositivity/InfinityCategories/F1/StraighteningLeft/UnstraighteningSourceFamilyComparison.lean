module

public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.LeftUnstraighteningMappingChoice
public import SerrePositivity.InfinityCategories.F1.Transport.PrismLiftSpace
public import SerrePositivity.InfinityCategories.F1.FunctorCategories.FunctorParameterizedPrismNaturality
public import SerrePositivity.InfinityCategories.F1.FunctorCategories.RelativeFunctorSquarePost

/-!
概要：任意の全空間からの pointed な実現を unstraightening 比較の前合成と結ぶ。
方針：普遍 prism を全空間とパラメーターで同時に制限し延長空間で比較する。
規約：全空間の射影の充填性や底の小ささを要求しない。
使われ方：一般の表現の写像空間比較の前後合成の可換式。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：任意の始域からの実現は unstraightening の比較の始域制限と関手同型。
方針：同じ始点と底を保つ二つの prism の終点を比較する。
規約：全パラメーターでの相対写像空間内の同型。
使われ方：選択表現の間の比較を標準 unstraightening の比較へ結ぶ。 -/
def unstraighteningSourceFamilyComparisonIso {E B K : SSet.{u + 1}}
    (F G : B ⟶ SpaceInfinity.{u}) (p : E ⟶ B)
    (i : E ⟶ leftUnstraightening F) (hi : i ≫ leftUnstraighteningProjection F = p)
    (t : K ⟶ leftUnstraighteningTransformationSpace F G)
    (f : E ⊗ K ⟶ leftUnstraightening G) (hf : f ≫ leftUnstraighteningProjection G = fst E K ≫ p)
    (W : ((Δ[1] : SSet.{u + 1}) ⊗ E) ⊗ K ⟶ PointedSpaceInfinity.{u})
    (hw₀ : (prismEndpoint 0 E ▷ K) ≫ W = fst E K ≫ i ≫ pullback.fst pointedSpaceProjection F)
    (hw₁ : (prismEndpoint 1 E ▷ K) ≫ W = f ≫ pullback.fst pointedSpaceProjection G)
    (hwp : W ≫ pointedSpaceProjection = ((Δ[1] ◁ p) ▷ K) ≫
      functorParameterizedPrism (intervalMappingUncurry t)) :
    FunctorIso ((t ≫ leftUnstraighteningMappingSpaceMap F G) ≫
      relativeFunctorOverPre (leftUnstraighteningProjection G)
        (Over.homMk (U := Over.mk p) (V := Over.mk (leftUnstraighteningProjection F)) i hi))
      (relativeFunctorCurry f hf) := by
  let T := leftUnstraighteningTransformationSpace F G
  let M := leftUnstraighteningMappingSpaceMap F G
  let P := (Δ[1] ◁ i) ⊗ₘ t
  let Z := P ≫ leftUnstraighteningTransformationFamilyLift F G
  let b := ((Δ[1] ◁ p) ▷ K) ≫ functorParameterizedPrism (intervalMappingUncurry t)
  have hend (j : Fin 2) : (prismEndpoint j E ▷ K) ≫ P =
      (i ⊗ₘ t) ≫ (prismEndpoint j (leftUnstraightening F) ▷ T) := by
    apply SSet.hom_ext; intro n; rfl
  have hbase : P ≫ ((Δ[1] ◁ leftUnstraighteningProjection F) ▷ T) =
      ((Δ[1] ◁ p) ▷ K) ≫ ((Δ[1] ⊗ B) ◁ t) := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    rintro ⟨⟨a, x⟩, k⟩
    change ((a, (leftUnstraighteningProjection F).app n (i.app n x)), t.app n k) =
      ((a, p.app n x), t.app n k)
    exact congrArg (fun z : B.obj n ↦ ((a, z), t.app n k))
      (congrArg (fun v : E ⟶ B ↦ v.app n x) hi)
  have hz : Z ≫ pointedSpaceProjection = b := by
    rw [Category.assoc, leftUnstraighteningTransformationFamilyLift_projection,
      ← Category.assoc, hbase, Category.assoc, leftUnstraighteningTransformationFamily_parameter]
  have hz₀ : (prismEndpoint 0 E ▷ K) ≫ Z =
      fst E K ≫ i ≫ pullback.fst pointedSpaceProjection F := by
    rw [← Category.assoc, hend, Category.assoc]
    change (i ⊗ₘ t) ≫ ((simplexPrismVertex 1 0 _ ▷ T) ≫ _) = _
    rw [leftUnstraighteningTransformationFamilyLift_start, ← Category.assoc]
    have hn : (i ⊗ₘ t) ≫ fst (leftUnstraightening F) T = fst E K ≫ i := by
      apply SSet.hom_ext; intro n; rfl
    rw [hn, Category.assoc]
  let g := (i ⊗ₘ t) ≫ relativeFunctorUncurry M
  let a : Over.mk p ⟶ Over.mk (leftUnstraighteningProjection F) := Over.homMk i hi
  let k := (t ≫ M) ≫ relativeFunctorOverPre (leftUnstraighteningProjection G) a
  have hgk : relativeFunctorUncurry k = g := by
    have hh := relativeFunctorOverPre_uncurry (leftUnstraighteningProjection G) a (t ≫ M)
    rw [relativeFunctorUncurry_naturality] at hh
    exact hh.trans (by apply SSet.hom_ext; intro n; rfl)
  have hg : g ≫ leftUnstraighteningProjection G = fst E K ≫ p := by
    rw [← hgk]
    exact relativeFunctorUncurry_projection k
  have hz₁ : (prismEndpoint 1 E ▷ K) ≫ Z = g ≫ pullback.fst pointedSpaceProjection G := by
    have h₁ : (prismEndpoint 1 (leftUnstraightening F) ▷ T) ≫
        leftUnstraighteningTransformationFamilyLift F G =
        relativeFunctorUncurry M ≫ pullback.fst pointedSpaceProjection G :=
      (leftUnstraighteningMappingSpaceMap_pointed F G).symm
    calc
      _ = (i ⊗ₘ t) ≫ ((prismEndpoint 1 (leftUnstraightening F) ▷ T) ≫
          leftUnstraighteningTransformationFamilyLift F G) := by
        rw [← Category.assoc, hend, Category.assoc]
      _ = (i ⊗ₘ t) ≫ (relativeFunctorUncurry M ≫ pullback.fst pointedSpaceProjection G) :=
        congrArg (fun v ↦ (i ⊗ₘ t) ≫ v) h₁
      _ = g ≫ pullback.fst pointedSpaceProjection G := (Category.assoc _ _ _).symm
  have hv : (fst E K ≫ i ≫ pullback.fst pointedSpaceProjection F) ≫ pointedSpaceProjection =
      (prismEndpoint 0 E ▷ K) ≫ b := by
    rw [← hw₀, Category.assoc, hwp]
  have hj : (prismEndpoint 1 E ▷ K) ≫ b = (fst E K ≫ p) ≫ G := by
    dsimp only [b]
    rw [← hwp, ← Category.assoc, hw₁, Category.assoc, pullback.condition, ← Category.assoc]
    exact congrArg (fun v ↦ v ≫ G) hf
  let η := relativeFunctorExtensionEndpoint_witnessIso pointedSpaceProjection b
    (prismEndpoint 0 E ▷ K)
    (leftAnodyneExtensions_whiskerRight _ (prismEndpoint_zero_leftAnodyne E) K)
    (fst E K ≫ i ≫ pullback.fst pointedSpaceProjection F) hv
    (prismEndpoint 1 E ▷ K) G (fst E K ≫ p) hj
    Z W hz hwp hz₀ hw₀ g f hg hf hz₁ hw₁
  have e := relativeFunctorCurryIso (leftUnstraighteningProjection G) p g f hg hf η
  have hc : relativeFunctorCurry g hg = k := by
    apply relativeFunctorUncurry_injective (leftUnstraighteningProjection G) p
    exact (relativeFunctorUncurry_curry g hg).trans hgk.symm
  rw [hc] at e
  exact e

end SerrePositivity.InfinityCategories
