module
public import SerrePositivity.KST.Fibration.RelativeSimplicialDiagram
public import SerrePositivity.KST.SConstruction.StructureMapCofibers

/-! # 全 gapped 図式の相対 S•

K-S• が固定した全 Ar 評価・再添字界面を使う。各成分の商像が可逆となる辺を
全高次単体とともに保持し、元の S• の全ての面・退化で単体的対象を構成する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.LocalizingInvariants
open SerrePositivity.KST.SConstruction
namespace SerrePositivity.KST.Fibration

/-- 全 Ar 頂点の単体圏に関する共変な再添字。 -/
def arVertexFunctor : SimplexCategory ⥤ Type u where
  obj n := (arNerve.{u} n.len) _⦋0⦌
  map θ := (arNerveMap θ.toOrderHom).app (Opposite.op ⦋0⦌)
  map_id _ := rfl
  map_comp _ _ := rfl

/-- 元の全 gapped 図式の指定 Ar 成分での評価。 -/
def sComponentEvaluation (B : SSet.{u}) (n : ℕ) (a : (arNerve n) _⦋0⦌) :
    sConstruction n B ⟶ B :=
  (gappedSubcomplex n B).ι ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt a

/-- 評価と面・退化の可換性は元の K-1/K-2 界面の厳密な式である。 -/
lemma sComponentEvaluation_reindex (B : SSet.{u}) {n m : SimplexCategoryᵒᵖ}
    (θ : n ⟶ m) (a : arVertexFunctor.obj m.unop) :
    (simplicialSConstruction B).map θ ≫ sComponentEvaluation B m.unop.len a =
      sComponentEvaluation B n.unop.len (arVertexFunctor.map θ.unop a) :=
  sMap_gapped_evaluate B θ.unop.toOrderHom a

/-- wS_n(B)：元の S_n(B) の各成分で商の core 条件を課す。 -/
def relativeSConstruction {B C : SSet.{u}} (q : B ⟶ C) (n : ℕ) :
    (sConstruction n B).Subcomplex :=
  relativeDiagram q (sComponentEvaluation B n)

instance relativeSConstruction_quasicategory {B C : SSet.{u}} [Quasicategory B]
    (q : B ⟶ C) (n : ℕ) : Quasicategory (relativeSConstruction q n : SSet.{u}) :=
  inferInstanceAs (Quasicategory (relativeDiagram q (sComponentEvaluation B n) : SSet.{u}))

/-- Verdier 列では、実辺の相対所属は全 Ar 成分の W 所属と同値。 -/
lemma relativeSConstruction_mem_edge_iff
    {A B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} {i : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B} {q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C}
    (h : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence i q) (n : ℕ) (s : (sConstruction n B.obj) _⦋1⦌) :
    s ∈ (relativeSConstruction q.hom n).obj (Opposite.op ⦋1⦌) ↔
      ∀ a, (sComponentEvaluation B.obj n a).app (Opposite.op ⦋1⦌) s ∈
        _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.weakEquivalences i :=
  relativeDiagram_mem_edge_iff h (sComponentEvaluation B.obj n) s

/-- 元の全 gapped S• に相対条件を課した単体的対象 wS•B。 -/
def relativeSimplicialSConstruction {B C : SSet.{u}} (q : B ⟶ C) :
    SimplicialObject SSet.{u} :=
  relativeSimplicialDiagram q (simplicialSConstruction B) arVertexFunctor
    (fun n => sComponentEvaluation B n.unop.len) (sComponentEvaluation_reindex B)

/-- wS•B から元の S•B への実包含。 -/
def relativeSimplicialSConstructionInclusion {B C : SSet.{u}} (q : B ⟶ C) :
    relativeSimplicialSConstruction q ⟶ simplicialSConstruction B :=
  relativeSimplicialDiagramInclusion q (simplicialSConstruction B) arVertexFunctor
    (fun n => sComponentEvaluation B n.unop.len) (sComponentEvaluation_reindex B)

/-- 元の core S•B から wS•B への、全ての面・退化と可換な包含。 -/
def relativeSimplicialSConstructionCoreInclusion {B C : SSet.{u}} (q : B ⟶ C) :
    simplicialSConstruction B ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreFunctor ⟶ relativeSimplicialSConstruction q :=
  relativeSimplicialDiagramCoreInclusion q (simplicialSConstruction B) arVertexFunctor
    (fun n => sComponentEvaluation B n.unop.len) (sComponentEvaluation_reindex B)

end SerrePositivity.KST.Fibration
