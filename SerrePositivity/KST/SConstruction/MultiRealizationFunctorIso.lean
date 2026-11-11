module
public import SerrePositivity.KST.SConstruction.StableMultiRealizationHomotopy
public import SerrePositivity.HomotopicalAlgebra.Simplicial.AnodyneHomotopyLocalization

/-! # 元の全反復実現射の関手同型不変性
概要：StableModel の完全射の関手同型は、元の反復実現射の局所化像を等しくする。
方針：同じ完全射を自然同値の core へ束ね、全反復の実ホモトピーを使う。
規約：零回を含む全有限反復、モデル圏引数なし。使われ方：K-1/K-2 の固定界面。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet
open SerrePositivity.InfinityCategories LocalizingInvariants SerrePositivity.SimplicialModel

/-- 同じ StableModel 完全射の関手同型は、元の全反復実現射の実ホモトピーになる。 -/
def multiRealizationHomotopyOfFunctorIso (r : ℕ) {X Y : StableModel.{u}} {f g : X ⟶ Y}
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f.val g.val) :
    SSet.Homotopy ((multiRealizationFunctor r).map f) ((multiRealizationFunctor r).map g) := by
  let C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u} := ⟨X.carrier, inferInstance, inferInstance⟩
  let D : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u} := ⟨Y.carrier, inferInstance, inferInstance⟩
  let F : C ⟶ D := ⟨f.val, ⟨f.property.1, f.property.2⟩⟩
  let G : C ⟶ D := ⟨g.val, ⟨g.property.1, g.property.2⟩⟩
  exact stableMultiRealizationHomotopyOfFunctorIso r (C := C) (D := D) (F := F) (G := G) e

/-- 同じ完全射の関手同型は、全有限反復実現の anodyne 局所化像を等しくする。 -/
lemma multiRealizationFunctor_map_localized_eq_of_functorIso (r : ℕ)
    {X Y : StableModel.{u}} {f g : X ⟶ Y} (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f.val g.val) :
    AnodyneHomotopy.anodyneQ.map ((multiRealizationFunctor r).map f) =
      AnodyneHomotopy.anodyneQ.map ((multiRealizationFunctor r).map g) :=
  AnodyneHomotopy.map_homotopy_eq AnodyneHomotopy.anodyneQ
    (Localization.inverts _ anodyneExtensions) (multiRealizationHomotopyOfFunctorIso r e)

/-- K-1/K-2 向け固定界面：正の全有限反復の元の射の局所化像は関手同型で不変。 -/
lemma multiRealization_map_positive_localized_eq_of_functorIso (r : ℕ)
    {X Y : StableModel.{u}} {f g : X ⟶ Y} (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f.val g.val) :
    AnodyneHomotopy.anodyneQ.map ((multiRealizationFunctor (r + 1)).map f) =
      AnodyneHomotopy.anodyneQ.map ((multiRealizationFunctor (r + 1)).map g) :=
  multiRealizationFunctor_map_localized_eq_of_functorIso (r + 1) e

end SerrePositivity.KST.SConstruction
