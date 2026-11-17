module
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.CofinalComposition
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.PrecompositionCofinality
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.RelativeFunctorVertices
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.RelativeFunctorPostcomposition

/-!
概要：同じ底上のleft fibrationsの間では、cofinalな射が前合成同値になる。
方針：二つの相対関手空間で恒等射を戻し、Kan空間の充満忠実性で余単位を戻す。
規約：元の射と厳密な底上の等式を保つ。
使われ方：元のGrothendieck–Kan比較の指定延長の検出。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- 相対前合成の二つの定義を、同じ底上の射で照合する。 -/
lemma IsLeftCofinal.relativeFunctorOverPre_isQCatEquivalence
    {T E F B : SSet.{u}} (r : T ⟶ B) [LeftFibration r]
    (p : E ⟶ B) (q : F ⟶ B) (f : E ⟶ F) (hf : f ≫ q = p)
    (hc : IsLeftCofinal f) :
    IsQCatEquivalence (relativeFunctorOverPre r (show Over.mk p ⟶ Over.mk q from Over.homMk f hf)) := by
  subst p
  have h := hc.restrictDiagram r q
  change IsSimplicialHomotopyEquivalence
    (relativeFunctorOverPre r (show Over.mk (f ≫ q) ⟶ Over.mk q from Over.homMk f rfl)) at h
  exact h.isQCatEquivalence

/-- 同じ底上のleft fibrationsの間のcofinal射は、元の射の前合成同値である。 -/
theorem isPrecompositionEquivalence_of_leftCofinal_overLeftFibrations
    {E F B : SSet.{u}} [Quasicategory B]
    (p : E ⟶ B) (q : F ⟶ B) [LeftFibration p] [LeftFibration q]
    (f : E ⟶ F) (hf : f ≫ q = p) (hc : IsLeftCofinal f) :
    IsPrecompositionEquivalence f := by
  have : Quasicategory E := quasicategory_of_innerFibration p
  have : Quasicategory F := quasicategory_of_innerFibration q
  let ff : Over.mk p ⟶ Over.mk q := Over.homMk f hf
  have hp := hc.relativeFunctorOverPre_isQCatEquivalence p p q f hf
  have hq := hc.relativeFunctorOverPre_isQCatEquivalence q p q f hf
  let e := relativeFunctorVertex p p (𝟙 E) (Category.id_comp p)
  obtain ⟨v, ⟨hv⟩⟩ := hp.choose.isEssentiallySurjective e
  obtain ⟨g, hg, rfl⟩ := exists_relativeFunctorVertex p q v
  have hunit : FunctorIso (f ≫ g) (𝟙 E) :=
    VertexIso.map hv (vertexFiberι ((ihom E).map p) (functorVertex p))
  let x := relativeFunctorVertex q q (g ≫ f) (by rw [Category.assoc, hf, hg])
  let y := relativeFunctorVertex q q (𝟙 F) (Category.id_comp q)
  have he : VertexIso
      ((relativeFunctorOverPre q ff).app (Opposite.op ⦋0⦌) x)
      ((relativeFunctorOverPre q ff).app (Opposite.op ⦋0⦌) y) := by
    let post :=
      SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorPost
        p q f hf p
    have h := VertexIso.map hv post
    convert h using 1
    · rfl
    · apply Subtype.ext
      change functorVertex (f ≫ (g ≫ f)) = functorVertex ((f ≫ g) ≫ f)
      rw [Category.assoc]
    · apply Subtype.ext
      change functorVertex (f ≫ 𝟙 F) = functorVertex ((𝟙 E) ≫ f)
      rw [Category.comp_id, Category.id_comp]
  have hcu : FunctorIso (g ≫ f) (𝟙 F) :=
    VertexIso.map (hq.isFullyFaithful.preimageVertexIso he)
      (vertexFiberι ((ihom F).map q) (functorVertex q))
  exact (show IsQCatEquivalence f from ⟨g, ⟨hunit⟩, ⟨hcu⟩⟩).isPrecompositionEquivalence
end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality
