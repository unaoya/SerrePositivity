module

public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.SimplicialPairCategory
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.NervePostcomposition

/-!
概要：Hom の直積による豊穣圏の coherent nerve を単体集合の積と同定する。
方針：豊穣射影と、同じ始域を持つ豊穣関手の対を次数ごとに使う。
規約：両成分は同じ対象宇宙を使い、局所 Kan 性は要求しない。
使われ方：二変数の共同評価を実際の関手圏に値を取る族へ curry する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v w
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial

/-- 積の豊穣圏の第一射影。 -/
def simplicialPairFst (C D : Type v)
    [Category.{u} C] [SimplicialCategory C] [Category.{u} D] [SimplicialCategory D] :
    EnrichedFunctor SSet.{u} (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.SimplicialPairObject C D) C where
  obj X := X.1
  map _X _Y := fst _ _
  map_id _ := rfl
  map_comp _ _ _ := rfl

/-- 積の豊穣圏の第二射影。 -/
def simplicialPairSnd (C D : Type v)
    [Category.{u} C] [SimplicialCategory C] [Category.{u} D] [SimplicialCategory D] :
    EnrichedFunctor SSet.{u} (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.SimplicialPairObject C D) D where
  obj X := X.2
  map _X _Y := snd _ _
  map_id _ := rfl
  map_comp _ _ _ := rfl

/-- 同じ始域を持つ二つの豊穣関手を対にする。 -/
def simplicialPairLift {A : Type w} {C D : Type v} [Category.{u} A] [SimplicialCategory A]
    [Category.{u} C] [SimplicialCategory C] [Category.{u} D] [SimplicialCategory D]
    (F : EnrichedFunctor SSet.{u} A C) (G : EnrichedFunctor SSet.{u} A D) :
    EnrichedFunctor SSet.{u} A (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.SimplicialPairObject C D) where
  obj X := (F.obj X, G.obj X)
  map X Y := lift (F.map X Y) (G.map X Y)
  map_id X := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro t
    apply Prod.ext
    · exact congrArg (fun k ↦ k.app n t) (F.map_id X)
    · exact congrArg (fun k ↦ k.app n t) (G.map_id X)
  map_comp X Y Z := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    rintro ⟨f, g⟩
    apply Prod.ext
    · exact congrArg (fun k ↦ k.app n (f, g)) (F.map_comp X Y Z)
    · exact congrArg (fun k ↦ k.app n (f, g)) (G.map_comp X Y Z)

/-- 豊穣圏の対の coherent nerve から成分の nerve の積への射。 -/
def simplicialPairNerveTo (C D : Type v)
    [Category.{u} C] [SimplicialCategory C] [Category.{u} D] [SimplicialCategory D] :
    SimplicialNerve (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.SimplicialPairObject C D) ⟶ SimplicialNerve C ⊗ SimplicialNerve D :=
  lift (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (simplicialPairFst C D)) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (simplicialPairSnd C D))

/-- 各次数の二つの coherent 図式を対にする逆射。 -/
def simplicialPairNerveFrom (C D : Type v)
    [Category.{u} C] [SimplicialCategory C] [Category.{u} D] [SimplicialCategory D] :
    SimplicialNerve C ⊗ SimplicialNerve D ⟶ SimplicialNerve (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.SimplicialPairObject C D) where
  app _ := ↾fun FG ↦ simplicialPairLift FG.1 FG.2
  naturality _ _ _ := rfl

/-- Hom の直積で作った圏の coherent nerve は実際の単体集合の積。 -/
def simplicialPairNerveIso (C D : Type v)
    [Category.{u} C] [SimplicialCategory C] [Category.{u} D] [SimplicialCategory D] :
    SimplicialNerve (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.SimplicialPairObject C D) ≅ SimplicialNerve C ⊗ SimplicialNerve D where
  hom := simplicialPairNerveTo C D
  inv := simplicialPairNerveFrom C D
  hom_inv_id := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro F
    apply EnrichedFunctor.ext SSet (fun _ ↦ rfl)
    intro X Y
    simp only [eqToHom_refl, Category.comp_id]
  inv_hom_id := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    rintro ⟨F, G⟩
    apply Prod.ext
    · apply EnrichedFunctor.ext SSet (fun _ ↦ rfl)
      intro X Y
      simp only [eqToHom_refl, Category.comp_id]
    · apply EnrichedFunctor.ext SSet (fun _ ↦ rfl)
      intro X Y
      simp only [eqToHom_refl, Category.comp_id]

/-- 積の同型の逆射は標準頂点の対を標準頂点へ写す。 -/
lemma simplicialPairNerveFrom_vertex {C D : Type v}
    [Category.{u} C] [SimplicialCategory C] [Category.{u} D] [SimplicialCategory D]
    (X : C) (Y : D) :
    (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.simplicialPairNerveFrom C D).app (Opposite.op ⦋0⦌)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex X, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex Y) =
        _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (show _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.SimplicialPairObject C D from (X, Y)) := by
  apply EnrichedFunctor.ext SSet (fun _ ↦ rfl)
  intro i j
  simp only [eqToHom_refl, Category.comp_id]

/-- 第一の頂点を固定した積の包含は既存の豊穣包含の coherent nerve。 -/
lemma simplicialPairNerveFrom_right {C D : Type v}
    [Category.{u} C] [SimplicialCategory C] [Category.{u} D] [SimplicialCategory D]
    (X : C) :
    lift (SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex X)) (𝟙 (SimplicialNerve D)) ≫
      _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.simplicialPairNerveFrom C D = _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.simplicialPairRightInclusion X D) := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro F
  apply EnrichedFunctor.ext SSet (fun _ ↦ rfl)
  intro i j
  simp only [eqToHom_refl, Category.comp_id]

end SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial
