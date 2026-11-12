module
public import SerrePositivity.KST.SConstruction.StableMultiSCoreDiagram
public import SerrePositivity.KST.SConstruction.SimplicialEnrichedDiagramFunctor

/-! # 全自然同値入力を持つ反復 core S• の対角図式
概要：全多単体作用を保持した反復 core 図式を、元の対角図式の内側の Hom へ束ねる。
方針：既存の全方向対角で前合成し、標準 end による厳密豊穣関手を適用する。
規約：内部対角の Kan 性は主張しない。使われ方：元の反復実現への全パラメータ接続。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open SerrePositivity.InfinityCategories LocalizingInvariants

/-- 全 S 方向を同じ次数へ制限した、元の反復 core S• の厳密豊穣図式。 -/
def stableMultiSCoreDiagonalDiagram (r : ℕ) :
    SimplicialObject (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.QuasicategoryEnrichedFunctorCategory _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u}) :=
  multiIndexDiagonal r ⋙ stableMultiSCoreEnrichedDiagram r

/-- 全自然同値入力を反復 core S• 対角図式全体へ送る厳密豊穣関手。 -/
def stableMultiSCoreObjectEnrichedFunctor (r : ℕ) :
    EnrichedFunctor SSet.{u} _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u}
      SimplicialSSetDiagram.{u} :=
  simplicialEnrichedDiagramFunctor (stableMultiSCoreDiagonalDiagram r)

/-- 豊穣作用の実値は、元の同じ全反復 core S• の対角図式。 -/
lemma stableMultiSCoreObjectEnrichedFunctor_obj (r : ℕ)
    (C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u}) :
    ((stableMultiSCoreObjectEnrichedFunctor r).obj C).diagram =
      multiIndexDiagonal r ⋙ multiCoreSConstruction r
        (stableCategoryModel (C)) := rfl

/-- 図式全体の各 Hom 射影は、元の同じ多次数の全自然同値入力族を回収する。 -/
lemma stableMultiSCoreObjectEnrichedFunctor_projection (r : ℕ)
    (C D : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u}) (n : SimplexCategoryᵒᵖ) :
    (stableMultiSCoreObjectEnrichedFunctor r).map C D ≫
      simplicialSSetDiagramProjection
        ((stableMultiSCoreObjectEnrichedFunctor r).obj C)
        ((stableMultiSCoreObjectEnrichedFunctor r).obj D) n =
      ((stableMultiSCoreEnrichedDiagram r).obj (fun _ => n)).map C D :=
  simplicialEnrichedDiagramFunctor_projection
    (stableMultiSCoreDiagonalDiagram r) C D n

/-- 通常の完全射による、元の同じ反復 core S• 対角図式の自然変換。 -/
def stableMultiSCoreObjectMap (r : ℕ)
    {C D : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u}} (F : C ⟶ D) :
    (stableMultiSCoreObjectEnrichedFunctor r).obj C ⟶
      (stableMultiSCoreObjectEnrichedFunctor r).obj D :=
  Functor.whiskerLeft (multiIndexDiagonal r)
    ((multiCoreSConstructionFunctor r).map
      ⟨(F).hom,
        @preservesCofiberData_of_isExactFunctor _ _ F.hom F.isExact⟩)

/-- 元の通常の完全射では、同じ元の反復 core 自然変換を全段で回収する。 -/
lemma stableMultiSCoreObjectEnrichedFunctor_hom (r : ℕ)
    {C D : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u}} (F : C ⟶ D) :
    eHomEquiv SSet.{u} F ≫
      (stableMultiSCoreObjectEnrichedFunctor r).map C D =
        eHomEquiv SSet.{u} (stableMultiSCoreObjectMap r F) := by
  apply simplicialSSetDiagramHom_ext
  intro n
  rw [Category.assoc, stableMultiSCoreObjectEnrichedFunctor_projection,
    simplicialSSetDiagramHomEquiv_projection]
  exact stableMultiSCoreEnrichedDiagram_hom r (fun _ => n) F

/-- 内部の単体方向も対角に取ると、同じ元の反復実現の実値を回収する。 -/
lemma stableMultiSCoreObjectEnrichedFunctor_realization (r : ℕ)
    (C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u}) :
    Functor.diag SimplexCategoryᵒᵖ ⋙ Functor.uncurry.obj
      ((stableMultiSCoreObjectEnrichedFunctor r).obj C).diagram =
        multiDiagonalCoreSConstruction r
          (stableCategoryModel (C)) := rfl

/-- 通常の完全射の対角像も、同じ元の反復実現の射を厳密に回収する。 -/
lemma stableMultiSCoreObjectMap_realization (r : ℕ)
    {C D : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u}} (F : C ⟶ D) :
    Functor.whiskerLeft (Functor.diag SimplexCategoryᵒᵖ)
      (Functor.uncurry.map (show
        ((stableMultiSCoreObjectEnrichedFunctor r).obj C).diagram ⟶
          ((stableMultiSCoreObjectEnrichedFunctor r).obj D).diagram from
            stableMultiSCoreObjectMap r F)) =
      (multiRealizationFunctor r).map
        ⟨(F).hom,
          @preservesCofiberData_of_isExactFunctor _ _ F.hom F.isExact⟩ := rfl

end SerrePositivity.KST.SConstruction
