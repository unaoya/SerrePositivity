module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.Homotopies.Reindexing.EnrichedFullSubcategoryRestriction
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.MapSmallness
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.VertexFiber
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Edges

/-!
概要：頂点が全充満部分圏に入る coherent な写像を、同じ部分圏の nerve へ制限する。
方針：各 simplex の全対象を頂点から回収し、同じ Hom で制限。
規約：元の包含との合成を保持。使われ方：cf 対応圏の端点 fiber と部分圏の nerve の同型。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u v w
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
noncomputable section
variable {C : Type v} [Category.{u} C] [SimplicialCategory C]
variable (P : ObjectProperty C)
/-- 元の豊穣包含が全次数で誘導する coherent nerve の射。 -/
def coherentFullSubcategoryInclusion : SimplicialNerve P.FullSubcategory ⟶ SimplicialNerve C :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.enrichedFullSubcategoryInclusion P)

/-- 全充満部分圏の対象と Hom の包含は coherent nerve 上でも単射。 -/
instance coherentFullSubcategoryInclusion_mono : Mono (coherentFullSubcategoryInclusion P) := by
  rw [NatTrans.mono_iff_mono_app]
  intro n
  rw [mono_iff_injective]
  exact _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.enrichedFullSubcategoryInclusion_comp_injective P

variable {X : SSet.{max u v}} (f : X ⟶ SimplicialNerve C)
  (h : ∀ x, P (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveObject (f.app (Opposite.op ⦋0⦌) x)))

/-- 頂点条件を持つ元の coherent simplex を部分圏へ制限する。 -/
def coherentFullSubcategoryLiftSimplex (n : SimplexCategoryᵒᵖ) (s : X.obj n) :
    (SimplicialNerve P.FullSubcategory).obj n :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.enrichedFullSubcategoryLift P (f.app n s) (fun i ↦ by
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentMap_simplex_obj f s i]
    exact h _)

/-- 制限した simplex は、包含後に元の simplex へ厳密に戻る。 -/
lemma coherentFullSubcategoryLiftSimplex_inclusion (n : SimplexCategoryᵒᵖ) (s : X.obj n) :
    (coherentFullSubcategoryInclusion P).app n
      (coherentFullSubcategoryLiftSimplex P f h n s) = f.app n s :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.enrichedFullSubcategoryLift_comp P _ _

/-- 頂点条件を持つ coherent な写像を部分圏の nerve へ制限する。 -/
def coherentFullSubcategoryLift : X ⟶ SimplicialNerve P.FullSubcategory where
  app n := ↾fun s ↦ coherentFullSubcategoryLiftSimplex P f h n s
  naturality {n m} α := by
    apply ConcreteCategory.hom_ext
    intro s
    apply _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.enrichedFullSubcategoryInclusion_comp_injective P
    change (coherentFullSubcategoryInclusion P).app m
      (coherentFullSubcategoryLiftSimplex P f h m (X.map α s)) =
        (coherentFullSubcategoryInclusion P).app m
          ((SimplicialNerve P.FullSubcategory).map α
            (coherentFullSubcategoryLiftSimplex P f h n s))
    rw [coherentFullSubcategoryLiftSimplex_inclusion]
    calc
      _ = (SimplicialNerve C).map α (f.app n s) :=
        ConcreteCategory.congr_hom (f.naturality α) s
      _ = (SimplicialNerve C).map α ((coherentFullSubcategoryInclusion P).app n
          (coherentFullSubcategoryLiftSimplex P f h n s)) := by
        rw [coherentFullSubcategoryLiftSimplex_inclusion]
      _ = _ := (ConcreteCategory.congr_hom
        ((coherentFullSubcategoryInclusion P).naturality α) _).symm

/-- 全次数の制限は元の包含と厳密に両立する。 -/
lemma coherentFullSubcategoryLift_inclusion :
    coherentFullSubcategoryLift P f h ≫ coherentFullSubcategoryInclusion P = f := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro s
  exact coherentFullSubcategoryLiftSimplex_inclusion P f h n s

variable {B : SSet.{max u v}} (p : SimplicialNerve C ⟶ B) (b : B _⦋0⦌)
  (hp : coherentFullSubcategoryInclusion P ≫ p = SSet.const b)
  (hP : ∀ x, p.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex x) = b → P x)

/-- 頂点 fiber の条件から全対象の条件を回収して部分圏へ戻す。 -/
def coherentFullSubcategoryFiberInverse : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p b ⟶ SimplicialNerve P.FullSubcategory :=
  coherentFullSubcategoryLift P (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p b) (fun s ↦ hP _ (by
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex_object]
    change p.app (Opposite.op ⦋0⦌) s.val = b
    exact s.property.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.constant_zero b)))

/-- 包含の定値性と fiber の頂点条件から、同じ部分圏の nerve と fiber を同型で結ぶ。 -/
def coherentFullSubcategoryFiberIso :
    SimplicialNerve P.FullSubcategory ≅ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p b where
  hom := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift p b (coherentFullSubcategoryInclusion P) hp
  inv := coherentFullSubcategoryFiberInverse P p b hP
  hom_inv_id := by
    apply (cancel_mono (coherentFullSubcategoryInclusion P)).1
    rw [Category.assoc, coherentFullSubcategoryFiberInverse,
      coherentFullSubcategoryLift_inclusion, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift_ι, Category.id_comp]
  inv_hom_id := by
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_hom_ext p b
    rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift_ι, coherentFullSubcategoryFiberInverse,
      coherentFullSubcategoryLift_inclusion, Category.id_comp]

/-- fiber 同型の元の全空間への合成は元の豊穣包含の nerve。 -/
lemma coherentFullSubcategoryFiberIso_hom_ι :
    (coherentFullSubcategoryFiberIso P p b hp hP).hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p b =
      coherentFullSubcategoryInclusion P := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift_ι p b _ hp

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
