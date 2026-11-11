module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.Functor
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.RelativeFunctorUnitHom
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.InnerFibrations.FullSubcomplexFibration
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.InnerFibrations.InnerFiber
public import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.Inner.PushoutProduct
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：cocartesian 辺を保つ元の底上の関手が張る相対関手 ∞ 圏。
方針：元の相対関手単体集合の頂点を底上の実際の射へ戻し、辺の保存条件で全部分複体を取る。
規約：Hom の全体は quasicategory。Kan 性は次に core を取って得る。
使われ方：Cat∞ 値分類で cocartesian fibrations の豊穣 Hom を構成する入力。

対応節は Kerodon 4.1（Tag 01B8）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.InnerFibrations

/-- 相対関手の頂点が、元の cocartesian 辺を保つ底上の実際の関手であるという条件。 -/
@[kerodon 02T1]
def cocartesianRelativeFunctorPredicate {E F B : SSet.{u}}
    (p : E ⟶ B) (q : F ⟶ B) (v : (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace q p) _⦋0⦌) : Prop :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.PreservesCocartesianEdges p q ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorVertexEquiv q p).symm v).val

/-- この頂点条件は、元の底上の射の辺の保存条件そのもの。 -/
lemma cocartesianRelativeFunctorPredicate_vertex {E F B : SSet.{u}}
    (p : E ⟶ B) (q : F ⟶ B) (f : E ⟶ F) (hf : f ≫ q = p) :
    cocartesianRelativeFunctorPredicate p q (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorVertex q p f hf) ↔
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.PreservesCocartesianEdges p q f := by
  change _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.PreservesCocartesianEdges p q
    (((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorVertexEquiv q p).symm ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorVertexEquiv q p) ⟨f, hf⟩)).val) ↔ _
  rw [Equiv.symm_apply_apply]

/-- 元の相対関手空間のうち、cocartesian 辺を保つ関手が張る全部分複体。 -/
@[kerodon 02T1]
def cocartesianRelativeFunctorSpace {E F B : SSet.{u}} (p : E ⟶ B) (q : F ⟶ B) : SSet.{u} :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace q p) (cocartesianRelativeFunctorPredicate p q)

/-- 標的の射影が inner fibration なら、元の相対関手空間は quasicategory。 -/
@[kerodon 01GS]
instance relativeFunctorSpace_quasicategory_of_innerFibration {E F B : SSet.{u}}
    (p : E ⟶ B) (q : F ⟶ B) [InnerFibration q] :
    Quasicategory (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace q p) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.InnerFibrations.innerFibration_vertexFiber_quasicategory ((ihom E).map q) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex p)

/-- cocartesian 関手が張る相対関手空間は、元の底の充填性を仮定せず quasicategory。 -/
instance cocartesianRelativeFunctorSpace_quasicategory {E F B : SSet.{u}}
    (p : E ⟶ B) (q : F ⟶ B) [InnerFibration q] :
    Quasicategory (cocartesianRelativeFunctorSpace p q) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.InnerFibrations.fullSubcomplexOnVertices_quasicategory _ _

/-- 元の相対豊穣合成は、指定した底上の二射の実際の合成を零単体で回収する。 -/
lemma relativeFunctorComposition_vertex {B : SSet.{u}} (a b c : Over B)
    (f : a.left ⟶ b.left) (hf : f ≫ b.hom = a.hom)
    (g : b.left ⟶ c.left) (hg : g ≫ c.hom = b.hom) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorComposition a b c).app (Opposite.op ⦋0⦌)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorVertex b.hom a.hom f hf, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorVertex c.hom b.hom g hg) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorVertex c.hom a.hom (f ≫ g) (by rw [Category.assoc, hg, hf]) := by
  apply Subtype.ext
  rfl

/-- 全ての高次の相対合成に対する頂点の保存条件は、元の関手の辺の保存の合成で閉じる。 -/
lemma cocartesianRelativeFunctorPredicate_comp {B : SSet.{u}} (a b c : Over B)
    (v : (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace b.hom a.hom) _⦋0⦌)
    (w : (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace c.hom b.hom) _⦋0⦌)
    (hv : cocartesianRelativeFunctorPredicate a.hom b.hom v)
    (hw : cocartesianRelativeFunctorPredicate b.hom c.hom w) :
    cocartesianRelativeFunctorPredicate a.hom c.hom
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorComposition a b c).app (Opposite.op ⦋0⦌) (v, w)) := by
  obtain ⟨f, hf, rfl⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.exists_relativeFunctorVertex b.hom a.hom v
  obtain ⟨g, hg, rfl⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.exists_relativeFunctorVertex c.hom b.hom w
  rw [relativeFunctorComposition_vertex, cocartesianRelativeFunctorPredicate_vertex]
  exact ((cocartesianRelativeFunctorPredicate_vertex _ _ _ _).mp hv).comp
    ((cocartesianRelativeFunctorPredicate_vertex _ _ _ _).mp hw)

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.InnerFibrations
