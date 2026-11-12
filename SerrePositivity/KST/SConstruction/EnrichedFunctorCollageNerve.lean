module
public import SerrePositivity.KST.SConstruction.EnrichedFunctorCollage

/-! # 有向 collage の局所 Kan 性・coherent nerve・射影
概要：有向 collage を通常の単体的圏にし、元の値域への豊穣射影を構成する。
方針：単位からの射による基礎圏を取り、上下段と交差 Hom の Kan 性を使う。
規約：下段の射影は恒等、上段は元の豊穣関手、交差 Hom の射影も恒等。
使われ方：元の全入力円柱を持ち上げ、交差 Hom の随伴で suspension 側へ運ぶ。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial
variable {C D : Type v} [Category.{u} C] [Category.{u} D]
  [SimplicialCategory C] [SimplicialCategory D]

/-- 単位からの射を通常の射とする、有向 collage の基礎圏。 -/
abbrev EnrichedFunctorCollageCategory (R : EnrichedFunctor SSet.{u} C D) :=
  ForgetEnrichment SSet.{u} (EnrichedFunctorCollage R)

/-- 有向 collage は元の Hom を持つ通常の単体的圏。 -/
instance enrichedFunctorCollage_simplicialCategory (R : EnrichedFunctor SSet.{u} C D) :
    SimplicialCategory (EnrichedFunctorCollageCategory R) := inferInstance

/-- 両段が局所 Kan なら交差 Hom と逆向きの空な Hom も含めて局所 Kan。 -/
instance enrichedFunctorCollage_sHom_kanComplex (R : EnrichedFunctor SSet.{u} C D)
    [∀ X Y : C, KanComplex (SimplicialCategory.sHom X Y)]
    [∀ X Y : D, KanComplex (SimplicialCategory.sHom X Y)]
    (X Y : EnrichedFunctorCollageCategory R) : KanComplex (SimplicialCategory.sHom X Y) := by
  rcases X with X | X <;> rcases Y with Y | Y
  · exact inferInstanceAs (KanComplex (SimplicialCategory.sHom X Y))
  · exact inferInstanceAs (KanComplex (SimplicialCategory.sHom X (R.obj Y)))
  · exact enrichedCollageEmpty_kanComplex
  · exact inferInstanceAs (KanComplex (SimplicialCategory.sHom X Y))

/-- 元の写像空間を保持する有向 collage の coherent nerve。 -/
def EnrichedFunctorCollageInfinity (R : EnrichedFunctor SSet.{u} C D) : SSet.{max u v} :=
  SimplicialNerve (EnrichedFunctorCollageCategory R)

/-- 両段が局所 Kan なら有向 collage の coherent nerve は ∞ 圏。 -/
instance enrichedFunctorCollageInfinity_quasicategory (R : EnrichedFunctor SSet.{u} C D)
    [∀ X Y : C, KanComplex (SimplicialCategory.sHom X Y)]
    [∀ X Y : D, KanComplex (SimplicialCategory.sHom X Y)] :
    Quasicategory (EnrichedFunctorCollageInfinity R) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.simplicialNerve_quasicategory (EnrichedFunctorCollageCategory R)

/-- 下段からの、元の全写像空間を保持する豊穣包含。 -/
def enrichedFunctorCollageBottom (R : EnrichedFunctor SSet.{u} C D) :
    EnrichedFunctor SSet.{u} D (EnrichedFunctorCollageCategory R) where
  obj X := ForgetEnrichment.of SSet (Sum.inl X : EnrichedFunctorCollage R)
  map X Y := 𝟙 (SimplicialCategory.sHom X Y)
  map_id X := Category.comp_id _
  map_comp X Y Z := by
    change eComp SSet X Y Z ≫ 𝟙 _ =
      (𝟙 (SimplicialCategory.sHom X Y) ⊗ₘ 𝟙 (SimplicialCategory.sHom Y Z)) ≫
        eComp SSet X Y Z
    simp only [Category.comp_id, tensorHom_id, id_whiskerRight, Category.id_comp]

/-- 上段からの、元の全写像空間を保持する豊穣包含。 -/
def enrichedFunctorCollageTop (R : EnrichedFunctor SSet.{u} C D) :
    EnrichedFunctor SSet.{u} C (EnrichedFunctorCollageCategory R) where
  obj X := ForgetEnrichment.of SSet (Sum.inr X : EnrichedFunctorCollage R)
  map X Y := 𝟙 (SimplicialCategory.sHom X Y)
  map_id X := Category.comp_id _
  map_comp X Y Z := by
    change eComp SSet X Y Z ≫ 𝟙 _ =
      (𝟙 (SimplicialCategory.sHom X Y) ⊗ₘ 𝟙 (SimplicialCategory.sHom Y Z)) ≫
        eComp SSet X Y Z
    simp only [Category.comp_id, tensorHom_id, id_whiskerRight, Category.id_comp]

/-- 射影は下段で恒等、上段で R の対象への作用。 -/
def enrichedFunctorCollageProjectionObj (R : EnrichedFunctor SSet.{u} C D)
    (X : EnrichedFunctorCollageCategory R) : D :=
  match X with
  | .inl X => X
  | .inr Y => R.obj Y

/-- 射影は下段と交差 Hom で恒等、上段で R の写像空間への作用。 -/
def enrichedFunctorCollageProjectionMap (R : EnrichedFunctor SSet.{u} C D)
    (X Y : EnrichedFunctorCollageCategory R) : SimplicialCategory.sHom X Y ⟶
      SimplicialCategory.sHom (enrichedFunctorCollageProjectionObj R X)
        (enrichedFunctorCollageProjectionObj R Y) :=
  match X, Y with
  | .inl X, .inl Y => 𝟙 (SimplicialCategory.sHom X Y)
  | .inl X, .inr Y => 𝟙 (SimplicialCategory.sHom X (R.obj Y))
  | .inr X, .inl Y => enrichedCollageEmptyMap (SimplicialCategory.sHom (R.obj X) Y)
  | .inr X, .inr Y => R.map X Y

/-- 元の値域への、全ての交差写像空間を厳密に保持する豊穣射影。 -/
def enrichedFunctorCollageProjection (R : EnrichedFunctor SSet.{u} C D) :
    EnrichedFunctor SSet.{u} (EnrichedFunctorCollageCategory R) D where
  obj := enrichedFunctorCollageProjectionObj R
  map := enrichedFunctorCollageProjectionMap R
  map_id X := by
    rcases X with X | X
    · exact Category.comp_id _
    · exact R.map_id X
  map_comp X Y Z := by
    change enrichedFunctorCollageComp R X Y Z ≫ enrichedFunctorCollageProjectionMap R X Z =
      (enrichedFunctorCollageProjectionMap R X Y ⊗ₘ
        enrichedFunctorCollageProjectionMap R Y Z) ≫
        eComp SSet (enrichedFunctorCollageProjectionObj R X)
          (enrichedFunctorCollageProjectionObj R Y) (enrichedFunctorCollageProjectionObj R Z)
    rcases X with X | X <;> rcases Y with Y | Y <;> rcases Z with Z | Z
    · change eComp SSet X Y Z ≫ 𝟙 _ =
        (𝟙 (SimplicialCategory.sHom X Y) ⊗ₘ 𝟙 (SimplicialCategory.sHom Y Z)) ≫
          eComp SSet X Y Z
      simp only [Category.comp_id, tensorHom_id, id_whiskerRight, Category.id_comp]
    · change eComp SSet X Y (R.obj Z) ≫ 𝟙 _ =
        (𝟙 (SimplicialCategory.sHom X Y) ⊗ₘ 𝟙 (SimplicialCategory.sHom Y (R.obj Z))) ≫
          eComp SSet X Y (R.obj Z)
      simp only [Category.comp_id, tensorHom_id, id_whiskerRight, Category.id_comp]
    · apply SSet.hom_ext
      intro n
      apply ConcreteCategory.hom_ext
      intro x
      exact PEmpty.elim x.2
    · exact Category.comp_id _
    · apply SSet.hom_ext
      intro n
      apply ConcreteCategory.hom_ext
      intro x
      exact PEmpty.elim x.1
    · apply SSet.hom_ext
      intro n
      apply ConcreteCategory.hom_ext
      intro x
      exact PEmpty.elim x.1
    · apply SSet.hom_ext
      intro n
      apply ConcreteCategory.hom_ext
      intro x
      exact PEmpty.elim x.2
    · exact R.map_comp X Y Z

/-- 射影と下段包含の合成は恒等豊穣関手そのもの。 -/
lemma enrichedFunctorCollageBottom_projection (R : EnrichedFunctor SSet.{u} C D) :
    (enrichedFunctorCollageBottom R).comp SSet (enrichedFunctorCollageProjection R) =
      EnrichedFunctor.id SSet D := by
  refine EnrichedFunctor.ext SSet (fun _ => ?_) ?_
  · rfl
  · intro X Y
    change (𝟙 (SimplicialCategory.sHom X Y) ≫ 𝟙 _) ≫ 𝟙 _ = 𝟙 _
    simp only [Category.comp_id]

/-- 射影と上段包含の合成は元の豊穣関手 R そのもの。 -/
lemma enrichedFunctorCollageTop_projection (R : EnrichedFunctor SSet.{u} C D) :
    (enrichedFunctorCollageTop R).comp SSet (enrichedFunctorCollageProjection R) = R := by
  refine EnrichedFunctor.ext SSet (fun _ => ?_) ?_
  · rfl
  · intro X Y
    change (𝟙 (SimplicialCategory.sHom X Y) ≫ R.map X Y) ≫ 𝟙 _ = R.map X Y
    simp only [Category.id_comp, Category.comp_id]

/-- 下段包含が全単体次数で誘導する coherent nerve の射。 -/
def enrichedFunctorCollageBottomInfinity (R : EnrichedFunctor SSet.{u} C D) :
    SimplicialNerve D ⟶ EnrichedFunctorCollageInfinity R :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (enrichedFunctorCollageBottom R)

/-- 上段包含が全単体次数で誘導する coherent nerve の射。 -/
def enrichedFunctorCollageTopInfinity (R : EnrichedFunctor SSet.{u} C D) :
    SimplicialNerve C ⟶ EnrichedFunctorCollageInfinity R :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (enrichedFunctorCollageTop R)

/-- 交差 Hom を保持する、元の値域への coherent nerve の射影。 -/
def enrichedFunctorCollageProjectionInfinity (R : EnrichedFunctor SSet.{u} C D) :
    EnrichedFunctorCollageInfinity R ⟶ SimplicialNerve D :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (enrichedFunctorCollageProjection R)

/-- 下段から戻る射影は全単体次数で恒等。 -/
lemma enrichedFunctorCollageBottomInfinity_projection (R : EnrichedFunctor SSet.{u} C D) :
    enrichedFunctorCollageBottomInfinity R ≫ enrichedFunctorCollageProjectionInfinity R =
      𝟙 (SimplicialNerve D) := by
  change _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (enrichedFunctorCollageBottom R) ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (enrichedFunctorCollageProjection R) = _
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap_comp, enrichedFunctorCollageBottom_projection, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap_id]

/-- 上段から戻る射影は全単体次数で元の R の coherent nerve の作用。 -/
lemma enrichedFunctorCollageTopInfinity_projection (R : EnrichedFunctor SSet.{u} C D) :
    enrichedFunctorCollageTopInfinity R ≫ enrichedFunctorCollageProjectionInfinity R =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap R := by
  change _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (enrichedFunctorCollageTop R) ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (enrichedFunctorCollageProjection R) = _
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap_comp, enrichedFunctorCollageTop_projection]

end SerrePositivity.KST.SConstruction
