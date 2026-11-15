module

public import SerrePositivity.InfinityCategories.Sheaves.LargeSiteSmallModel
public import SerrePositivity.InfinityCategories.Sheaves.SheafSiteEquivalence

/-!
概要：元の大きい site の層の全部分準圏を、同じ係数の小さい模型の層圏と比較する。
方針：元の全前層の再添字を、元の層条件の保存・反映により制限する。
使われ方：HTT 6.2.2.6、Kerodon §4.5.1（Tag 01DQ）の本質的小さい site の層圏。
規約：射・全高次単体を保つ。同じ universe の再添字の等式を保持する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories
open SerrePositivity.InfinityCategories.Project.FilteredExchange
open SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories
namespace SerrePositivity.InfinityCategories.Sheaves
variable {C : Type (u + 1)} [Category.{u} C] {D : Type u} [SmallCategory D]
variable {E : SSet.{u + 1}} [Quasicategory E]

/-- 元の大きい site の全前層準圏。係数の universe を変更しない。 -/
abbrev LargePresheafCat (C : Type (u + 1)) [Category.{u} C] (E : SSet.{u + 1}) :=
  (ihom (nerve Cᵒᵖ)).obj E

/-- 元の大きい前層の頂点を、同じ単体的集合の射へ読み戻す。 -/
def largeVertexToPresheaf (v : (LargePresheafCat C E) _⦋0⦌) : nerve Cᵒᵖ ⟶ E :=
  (functorVertexEquiv _ _).symm v

/-- 元の全被覆篩の層条件を、大きい全前層圏の頂点条件として保持する。 -/
def largeSheafProperty (K : GrothendieckTopology C) :
    (LargePresheafCat C E) _⦋0⦌ → Prop := fun v ↦ LargeIsSheaf K (largeVertexToPresheaf v)

/-- 元の大きい site の層の全部分準圏。 -/
abbrev LargeSheafCat (K : GrothendieckTopology C) (E : SSet.{u + 1}) [Quasicategory E] :=
  (fullSubcomplexOnVertices (LargePresheafCat C E) (largeSheafProperty K) : SSet.{u + 1})

/-- 元の層圏の全前層圏への包含。 -/
def largeSheafInclusion (K : GrothendieckTopology C) :
    LargeSheafCat K E ⟶ LargePresheafCat C E :=
  (fullSubcomplexOnVertices (LargePresheafCat C E) (largeSheafProperty K)).ι

/-- 小さい模型への全再添字は、元の前層の頂点の読み戻しと可換。 -/
lemma vertexToPresheaf_reindexSmallModel (e : D ≌ C) (v : (LargePresheafCat C E) _⦋0⦌) :
    vertexToPresheaf ((reindexSmallModelPresheafFunctor e E).app _ v) =
      (siteSmallModelShapeEquivalence e).hom ≫ largeVertexToPresheaf v :=
  functorVertexMap_precomp (siteSmallModelShapeEquivalence e).hom v

/-- 元の大きい層条件と小さい模型の層条件は、全再添字の頂点で一致する。 -/
lemma largeSheafProperty_smallModel_iff (e : D ≌ C)
    (J : GrothendieckTopology D) (K : GrothendieckTopology C)
    (hf : CoverPreserving J K e.functor) (hg : CoverPreserving K J e.inverse)
    (v : (LargePresheafCat C E) _⦋0⦌) :
    sheafProperty J ((reindexSmallModelPresheafFunctor e E).app _ v) ↔
      largeSheafProperty K v := by
  dsimp only [sheafProperty, largeSheafProperty]
  rw [vertexToPresheaf_reindexSmallModel]
  exact largeIsSheaf_smallModel_iff e J K hf hg _

/-- 小さい模型への全再添字を、元の大きい層の全部分準圏へ制限する。 -/
def reindexLargeSheafFunctor (e : D ≌ C)
    (J : GrothendieckTopology D) (K : GrothendieckTopology C)
    (hf : CoverPreserving J K e.functor) (hg : CoverPreserving K J e.inverse) :
    LargeSheafCat K E ⟶ SheafCat J E :=
  fullSubcomplexLift (sheafProperty (E := E) J)
    (largeSheafInclusion K ≫ reindexSmallModelPresheafFunctor e E)
    (fun x ↦ (largeSheafProperty_smallModel_iff e J K hf hg x.val).mpr
      (fullSubcomplexOnVertices_vertex x))

/-- 元の全前層への包含と、小さい模型への全再添字は厳密に可換。 -/
lemma reindexLargeSheafFunctor_comp (e : D ≌ C)
    (J : GrothendieckTopology D) (K : GrothendieckTopology C)
    (hf : CoverPreserving J K e.functor) (hg : CoverPreserving K J e.inverse) :
    reindexLargeSheafFunctor (E := E) e J K hf hg ≫ sheafInclusion J =
      largeSheafInclusion K ≫ reindexSmallModelPresheafFunctor e E :=
  fullSubcomplexLift_ι _ _ _

/-- 小さい模型への全再添字は、元の大きい層圏と小さい層圏の同値である。 -/
theorem reindexLargeSheafFunctor_isQCatEquivalence (e : D ≌ C)
    (J : GrothendieckTopology D) (K : GrothendieckTopology C)
    (hf : CoverPreserving J K e.functor) (hg : CoverPreserving K J e.inverse) :
    IsQCatEquivalence (reindexLargeSheafFunctor (E := E) e J K hf hg) := by
  apply isQCatEquivalence_fullSubcomplexRestriction
    (largeSheafProperty (E := E) K) (sheafProperty (E := E) J)
    (fun h ↦ sheafProperty_iff_of_vertexIso J h)
    (reindexSmallModelPresheafFunctor e E) (reindexSmallModelPresheafFunctor_isQCatEquivalence e)
    _ (reindexLargeSheafFunctor_comp e J K hf hg)
  intro x hx
  exact (largeSheafProperty_smallModel_iff e J K hf hg x).mp hx

end SerrePositivity.InfinityCategories.Sheaves
