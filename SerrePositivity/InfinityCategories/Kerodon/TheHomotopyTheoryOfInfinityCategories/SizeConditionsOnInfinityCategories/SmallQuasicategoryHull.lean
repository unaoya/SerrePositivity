module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.SmallInnerHornClosure
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.SmallSimplicialModel
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.UniverseSSetMaps

/-!
概要：小さい種を厳密に保持する、元の大きい quasicategory 内の小さい模型。
方針：同じ内ホーン充填閉包を Shrink し、その同型を通して全図式を因子化する。
規約：因子化は射の厳密な等号で与え、追加の存在仮定を入れない。
使われ方：Ind-S (4)、大きい標的での小さい図式・ホモトピー資料の回収。

対応節は Kerodon 4.9（Tag 03PP）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories

/-- 同じ種を含み、その種に入る全小図式を同時に厳密因子化する小さい quasicategory。 -/
structure Hull (X : SSet.{max u v}) (A : X.Subcomplex) where
  obj : SSet.{u}
  quasicategory : Quasicategory obj
  inclusion : (SSet.uliftFunctor.{v, u}).obj obj ⟶ X
  mono : Mono inclusion
  contains : A ≤ SSet.Subcomplex.range inclusion
  factor : ∀ {K : SSet.{u}} (f : (SSet.uliftFunctor.{v, u}).obj K ⟶ X),
    SSet.Subcomplex.range f ≤ A →
      ∃ g : K ⟶ obj, (SSet.uliftFunctor.{v, u}).map g ≫ inclusion = f

/-- 小さい種から、同じ ambient 内の小さい全充填模型と全図式の厳密因子化を構成する。 -/
def hull {X : SSet.{max u v}} [Quasicategory X] (A : X.Subcomplex)
    [∀ d, Small.{u} (A.obj d)] : Hull.{u, v} X A := by
  let C := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.innerHornClosure A
  have (d : SimplexCategoryᵒᵖ) : Small.{u} (C.toSSet.obj d) := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.small_innerHornClosure A d
  let e := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.modelIso.{u, v} C.toSSet
  refine {
    obj := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.model C.toSSet
    quasicategory := inferInstance
    inclusion := e.hom ≫ C.ι
    mono := inferInstance
    contains := ?_
    factor := ?_ }
  · intro d x hx
    let y : C.toSSet.obj d := ⟨x, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.le_innerHornClosure A _ hx⟩
    refine ⟨e.inv.app d y, ?_⟩
    have h := congrArg (fun k => k.app d y) e.inv_hom_id
    exact congrArg Subtype.val h
  · intro K f hf
    let t := C.lift f (le_trans hf (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.le_innerHornClosure A)) ≫ e.inv
    let g := (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftSSetFullyFaithful.{u, v}).preimage t
    refine ⟨g, ?_⟩
    rw [(_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftSSetFullyFaithful.{u, v}).map_preimage]
    simp only [t, Category.assoc, Iso.inv_hom_id_assoc, SSet.Subcomplex.lift_ι]

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories
