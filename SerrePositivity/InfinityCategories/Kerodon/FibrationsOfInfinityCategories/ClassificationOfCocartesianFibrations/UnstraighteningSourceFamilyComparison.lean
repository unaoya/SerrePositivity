module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftUnstraighteningMappingChoice
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.PrismLiftSpace
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.FunctorParameterizedPrismNaturality
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.RelativeFunctorSquarePost

/-!
概要：任意の全空間からの pointed な実現を unstraightening 比較の前合成と結ぶ。
方針：普遍 prism を全空間とパラメーターで同時に制限し延長空間で比較する。
規約：全空間の射影の充填性や底の小ささを要求しない。
使われ方：一般の表現の写像空間比較の前後合成の可換式。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- 概要：任意の始域からの実現は unstraightening の比較の始域制限と関手同型。
方針：同じ始点と底を保つ二つの prism の終点を比較する。
規約：全パラメーターでの相対写像空間内の同型。
使われ方：選択表現の間の比較を標準 unstraightening の比較へ結ぶ。 -/
def unstraighteningSourceFamilyComparisonIso {E B K : SSet.{u + 1}}
    (F G : B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}) (p : E ⟶ B)
    (i : E ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraightening F) (hi : i ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningProjection F = p)
    (t : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningTransformationSpace F G)
    (f : E ⊗ K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraightening G) (hf : f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningProjection G = fst E K ≫ p)
    (W : ((Δ[1] : SSet.{u + 1}) ⊗ E) ⊗ K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.PointedSpaceInfinity.{u})
    (hw₀ : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 E ▷ K) ≫ W = fst E K ≫ i ≫ pullback.fst _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection F)
    (hw₁ : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 E ▷ K) ≫ W = f ≫ pullback.fst _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection G)
    (hwp : W ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection = ((Δ[1] ◁ p) ▷ K) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.functorParameterizedPrism (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry t)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso ((t ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningMappingSpaceMap F G) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorOverPre (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningProjection G)
        (Over.homMk (U := Over.mk p) (V := Over.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningProjection F)) i hi))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorCurry f hf) := by
  let T := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningTransformationSpace F G
  let M := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningMappingSpaceMap F G
  let P := (Δ[1] ◁ i) ⊗ₘ t
  let Z := P ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningTransformationFamilyLift F G
  let b := ((Δ[1] ◁ p) ▷ K) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.functorParameterizedPrism (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry t)
  have hend (j : Fin 2) : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint j E ▷ K) ≫ P =
      (i ⊗ₘ t) ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint j (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraightening F) ▷ T) := by
    apply SSet.hom_ext; intro n; rfl
  have hbase : P ≫ ((Δ[1] ◁ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningProjection F) ▷ T) =
      ((Δ[1] ◁ p) ▷ K) ≫ ((Δ[1] ⊗ B) ◁ t) := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    rintro ⟨⟨a, x⟩, k⟩
    change ((a, (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningProjection F).app n (i.app n x)), t.app n k) =
      ((a, p.app n x), t.app n k)
    exact congrArg (fun z : B.obj n ↦ ((a, z), t.app n k))
      (congrArg (fun v : E ⟶ B ↦ v.app n x) hi)
  have hz : Z ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection = b := by
    rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningTransformationFamilyLift_projection,
      ← Category.assoc, hbase, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningTransformationFamily_parameter]
  have hz₀ : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 E ▷ K) ≫ Z =
      fst E K ≫ i ≫ pullback.fst _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection F := by
    rw [← Category.assoc, hend, Category.assoc]
    change (i ⊗ₘ t) ≫ ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.simplexPrismVertex 1 0 _ ▷ T) ≫ _) = _
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningTransformationFamilyLift_start, ← Category.assoc]
    have hn : (i ⊗ₘ t) ≫ fst (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraightening F) T = fst E K ≫ i := by
      apply SSet.hom_ext; intro n; rfl
    rw [hn, Category.assoc]
  let g := (i ⊗ₘ t) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry M
  let a : Over.mk p ⟶ Over.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningProjection F) := Over.homMk i hi
  let k := (t ≫ M) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorOverPre (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningProjection G) a
  have hgk : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry k = g := by
    have hh := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorOverPre_uncurry (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningProjection G) a (t ≫ M)
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorUncurry_naturality] at hh
    exact hh.trans (by apply SSet.hom_ext; intro n; rfl)
  have hg : g ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningProjection G = fst E K ≫ p := by
    rw [← hgk]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry_projection k
  have hz₁ : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 E ▷ K) ≫ Z = g ≫ pullback.fst _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection G := by
    have h₁ : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraightening F) ▷ T) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningTransformationFamilyLift F G =
        _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry M ≫ pullback.fst _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection G :=
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningMappingSpaceMap_pointed F G).symm
    calc
      _ = (i ⊗ₘ t) ≫ ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraightening F) ▷ T) ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningTransformationFamilyLift F G) := by
        rw [← Category.assoc, hend, Category.assoc]
      _ = (i ⊗ₘ t) ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry M ≫ pullback.fst _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection G) :=
        congrArg (fun v ↦ (i ⊗ₘ t) ≫ v) h₁
      _ = g ≫ pullback.fst _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection G := (Category.assoc _ _ _).symm
  have hv : (fst E K ≫ i ≫ pullback.fst _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection F) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 E ▷ K) ≫ b := by
    rw [← hw₀, Category.assoc, hwp]
  have hj : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 E ▷ K) ≫ b = (fst E K ≫ p) ≫ G := by
    dsimp only [b]
    rw [← hwp, ← Category.assoc, hw₁, Category.assoc, pullback.condition, ← Category.assoc]
    exact congrArg (fun v ↦ v ≫ G) hf
  let η := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorExtensionEndpoint_witnessIso _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection b
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 E ▷ K)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftAnodyneExtensions_whiskerRight _ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.prismEndpoint_zero_leftAnodyne E) K)
    (fst E K ≫ i ≫ pullback.fst _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection F) hv
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 E ▷ K) G (fst E K ≫ p) hj
    Z W hz hwp hz₀ hw₀ g f hg hf hz₁ hw₁
  have e := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorCurryIso (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningProjection G) p g f hg hf η
  have hc : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorCurry g hg = k := by
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry_injective (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningProjection G) p
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry_curry g hg).trans hgk.symm
  rw [hc] at e
  exact e

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
