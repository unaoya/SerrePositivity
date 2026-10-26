module
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomTargetNerveLaxComparison
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomMappingModel
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomotopyIsoPrecomposition
public import SerrePositivity.InfinityCategories.F2.CatInfinity.LaxPullbackMapping
public import SerrePositivity.InfinityCategories.Core.FullyFaithful
/-!
概要：元 Hom gluing の同じ Hom 複体から、元二脚の lax 写像空間への実比較。
方針：元 nerve の Hom 模型同型と F2 の実 Hom pullback 表示を合成する。
規約：元比較の実作用を保ち、同値性を新しい主経路の仮定にはしない。
使われ方：元終域の全 Hom 比較を左右入力・比較辺全族のまま検証する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types true
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits MonoidalCategory DifferentialGraded DGNerve SSet
open KST.SConstruction
open scoped Simplicial
variable (R : Type u) [CommRing R]
  (C D E : Type (max (u + 1) v)) [DGCategory R C] [Small.{u} C]
  [DGCategory R D] [DGCategory R E] [Small.{u} E]
  (p : DGFunctor R C E) (q : DGFunctor R D E)
local notation "M" => dgHomGluingBimodule R C D E p q
local notation "G" => DGGluingObject R C D M
local notation "F" => dgGluingHomTargetNerveLaxComparison R C D E p q
variable (X Y : DGGluingObject R C D (dgHomGluingBimodule R C D E p q))

def dgGluingHomTargetLaxHomMappingComparison :
    complexPinchedSpace.{u, max (u + 1) v} (dgGluingHomComplex R C D M X Y) ⟶
      InfinityCategories.pinchedHom ((F).app (Opposite.op ⦋0⦌) (Simplex.vertex X))
        ((F).app (Opposite.op ⦋0⦌) (Simplex.vertex Y)) :=
  (dgGluingHomMappingIso R C D M X Y).inv ≫ pinchedHomMap (F) (Simplex.vertex X) (Simplex.vertex Y)

def dgGluingHomTargetLaxHomPullback : SSet.{max (u + 1) v} :=
  pullback
    (pinchedHomMap (F2.arrowEndpointPair (dgNerve R E))
      ((F2.laxPullbackArrow (dgNerve.map p) (dgNerve.map q)).app (Opposite.op ⦋0⦌)
        ((F).app (Opposite.op ⦋0⦌) (Simplex.vertex X)))
      ((F2.laxPullbackArrow (dgNerve.map p) (dgNerve.map q)).app (Opposite.op ⦋0⦌)
        ((F).app (Opposite.op ⦋0⦌) (Simplex.vertex Y))))
    (pinchedHomPullbackBaseMap (F2.arrowEndpointPair (dgNerve R E))
      (dgNerve.map p ⊗ₘ dgNerve.map q)
      ((F).app (Opposite.op ⦋0⦌) (Simplex.vertex X))
      ((F).app (Opposite.op ⦋0⦌) (Simplex.vertex Y)))

/-- 同じ Hom 複体から元二脚の Hom pullback 表示への指定比較。 -/
def dgGluingHomTargetLaxHomPullbackComparison :
    complexPinchedSpace.{u, max (u + 1) v} (dgGluingHomComplex R C D M X Y) ⟶
      dgGluingHomTargetLaxHomPullback R C D E p q X Y :=
  dgGluingHomTargetLaxHomMappingComparison R C D E p q X Y ≫
    (F2.laxPullbackMappingIso (dgNerve.map p) (dgNerve.map q)
      ((F).app (Opposite.op ⦋0⦌) (Simplex.vertex X))
      ((F).app (Opposite.op ⦋0⦌) (Simplex.vertex Y))).hom

lemma dgGluingHomTargetLaxHomPullbackComparison_equivalence_iff :
    IsSimplicialHomotopyEquivalence
      (dgGluingHomTargetLaxHomPullbackComparison R C D E p q X Y) ↔
    IsSimplicialHomotopyEquivalence (pinchedHomMap (F) (Simplex.vertex X) (Simplex.vertex Y)) := by
  rw [dgGluingHomTargetLaxHomPullbackComparison,
    dgGluingHomotopyEquivalence_postcomp_iso_iff,
    dgGluingHomTargetLaxHomMappingComparison]
  exact dgGluingHomotopyEquivalence_precomp_iso_iff
    (dgGluingHomMappingIso R C D M X Y).symm _

/-- 元比較の充満忠実性は、この実 Hom 比較の同値性そのものである。 -/
lemma dgGluingHomTargetNerveLaxComparison_fullyFaithful_iff :
    IsFullyFaithful (F) ↔ ∀ X Y : G,
      IsSimplicialHomotopyEquivalence
        (dgGluingHomTargetLaxHomPullbackComparison R C D E p q X Y) := by
  constructor
  · intro h X Y
    exact (dgGluingHomTargetLaxHomPullbackComparison_equivalence_iff R C D E p q X Y).2
      (h _ _)
  · intro h x y
    obtain ⟨X, rfl⟩ := (Simplex.vertexEquiv (A := R) (D := G)).symm.surjective x
    obtain ⟨Y, rfl⟩ := (Simplex.vertexEquiv (A := R) (D := G)).symm.surjective y
    exact (dgGluingHomTargetLaxHomPullbackComparison_equivalence_iff R C D E p q X Y).1
      (h X Y)

end SerrePositivity.InfinityCategories
