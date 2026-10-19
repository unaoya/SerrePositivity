module
public import SerrePositivity.InfinityCategories.Derived.DGFunctorPinchedMap
public import SerrePositivity.InfinityCategories.Derived.PinchedChainMapTrivialFibration
public import SerrePositivity.DifferentialGraded.Functor.QuasiEquivalence

/-! # 全射 Hom 準同型な dg 関手の nerve の充満忠実性

概要：対象上全射性を仮定せず、全 Hom 上の全射準同型から充満忠実性を得る。
方針：写像空間の射を Hom 鎖写像の射と同定し、実際の全相対境界を充填する。
規約：充満忠実性は Core の実写像空間による定義。使われ方：β3 の前三角化との比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
open scoped Simplicial
variable {A : Type u} [CommRing A] {D E : Type v} [DGCategory A D] [DGCategory A E]

/-- 標準頂点間の実際の写像空間への作用は自明 Kan fibration。 -/
lemma dgFunctor_pinchedHomMap_trivialKanFibration (F : DGFunctor A D E)
    (hs : ∀ x y (i : ℤ), Function.Surjective ((F.map x y).f i))
    (hq : HomQuasiIso F) (x y : D) :
    TrivialKanFibration (pinchedHomMap (dgNerve.map F) (Simplex.vertex x) (Simplex.vertex y)) := by
  let e := pinchedEndpointIso (dgFunctorNerve_vertex F x) (dgFunctorNerve_vertex F y)
  have h := pinchedHomChainMap_trivialKanFibration (F.map x y) (hs x y) (hq x y)
  have he : pinchedHomMap (dgNerve.map F) (Simplex.vertex x) (Simplex.vertex y) =
      pinchedHomChainMap (F.map x y) ≫ e.inv := by
    rw [← dgFunctor_pinchedHomMap_eq]
    change _ = (_ ≫ e.hom) ≫ e.inv
    rw [Category.assoc, e.hom_inv_id, Category.comp_id]
  rw [he]
  constructor
  exact trivialKanFibrations.comp_mem _ _ h.mem (MorphismProperty.rlp_of_isIso _ _)

/-- 対象上全射性を要しない、全射 Hom 準同型な dg 関手の nerve の充満忠実性。 -/
lemma dgNerve_map_isFullyFaithful_of_surjective_quasiIso (F : DGFunctor A D E)
    (hs : ∀ x y (i : ℤ), Function.Surjective ((F.map x y).f i))
    (hq : HomQuasiIso F) : IsFullyFaithful (dgNerve.map F) := by
  intro x y
  obtain ⟨x, rfl⟩ := Simplex.vertexEquiv.symm.surjective x
  obtain ⟨y, rfl⟩ := Simplex.vertexEquiv.symm.surjective y
  change IsSimplicialHomotopyEquivalence
    (pinchedHomMap (dgNerve.map F) (Simplex.vertex x) (Simplex.vertex y))
  let := dgFunctor_pinchedHomMap_trivialKanFibration F hs hq x y
  exact (isQCatEquivalence_of_trivialKanFibration _).isSimplicialHomotopyEquivalence

/-- Hom 複体上の同型を持つ dg 関手は実際の ∞ 写像空間で充満忠実。 -/
lemma dgNerve_map_isFullyFaithful_of_homIso (F : DGFunctor A D E)
    (hi : ∀ x y, IsIso (F.map x y)) : IsFullyFaithful (dgNerve.map F) := by
  apply dgNerve_map_isFullyFaithful_of_surjective_quasiIso F
  · intro x y i
    let := hi x y
    exact (ConcreteCategory.bijective_of_isIso ((F.map x y).f i)).2
  · intro x y
    let := hi x y
    infer_instance

end SerrePositivity.InfinityCategories
