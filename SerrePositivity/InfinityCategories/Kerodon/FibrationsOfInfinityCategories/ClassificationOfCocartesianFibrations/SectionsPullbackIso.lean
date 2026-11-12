module

public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.RelativeFunctorIsPullbackIso
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.PullbackEdgeReflection
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.CocartesianSections
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.FullSubcomplexIso

/-!
概要：任意の底変換上の cocartesian section を、元の標的への同じ section と厳密に同型化する。
方針：全相対関手空間の pullback 同型を、元の辺の保存・反映で全部分複体へ制限する。
規約：可変の底と section の始域の quasicategory 性は不要。
使われ方：strict transport の底変換の比較を実際の section の作用として構成する。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

variable {X P E A B : SSet.{u}} [Quasicategory B] {p : E ⟶ B} [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianFibration p]
  {i : P ⟶ E} {r : P ⟶ A} {f : A ⟶ B} (hs : IsPullback i r p f)
  (a : X ⟶ A) (b : X ⟶ B) (hab : a ≫ f = b)

/-- 同じ全相対 Hom の pullback 同型は、全ての辺を cocartesian に送る条件を反映する。 -/
lemma cocartesianSectionsPullbackIso_predicate (v : (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace r a) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.IsCocartesianSection r a v ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.IsCocartesianSection p b
      ((_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.relativeFunctorIsPullbackIso hs a b hab).hom.app (Opposite.op ⦋0⦌) v) := by
  obtain ⟨g, hg, rfl⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.exists_relativeFunctorVertex r a v
  rw [_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.relativeFunctorIsPullbackIso_vertex]
  change (∀ e, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCocartesianEdge r (g.app (Opposite.op ⦋1⦌) e)) ↔
    (∀ e, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCocartesianEdge p (i.app (Opposite.op ⦋1⦌)
      (g.app (Opposite.op ⦋1⦌) e)))
  exact forall_congr' (fun e ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.isCocartesianEdge_isPullback_iff p hs (g.app _ e))

/-- 元の各底変換の cocartesian section と、元の標的へ写す同じ section の厳密な同型。 -/
def cocartesianSectionsPullbackIso : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianSections r a ≅ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianSections p b :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fullSubcomplexIso (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.relativeFunctorIsPullbackIso hs a b hab)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.IsCocartesianSection r a) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.IsCocartesianSection p b)
    (cocartesianSectionsPullbackIso_predicate hs a b hab)

/-- 同じ section 同型は、包含後に元の全相対 Hom の同型を回収する。 -/
lemma cocartesianSectionsPullbackIso_hom_ι :
    (cocartesianSectionsPullbackIso hs a b hab).hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianSectionsι p b =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianSectionsι r a ≫ (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.relativeFunctorIsPullbackIso hs a b hab).hom :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fullSubcomplexIso_hom_ι _ _ _ _

/-- 全パラメーターでの同じ section 同型の展開は、元の全空間への実際の後合成。 -/
lemma cocartesianSectionsPullbackIso_hom_uncurry {T : SSet.{u}}
    (k : T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianSections r a) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry ((k ≫ (cocartesianSectionsPullbackIso hs a b hab).hom) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianSectionsι p b) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry (k ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianSectionsι r a) ≫ i := by
  rw [Category.assoc, cocartesianSectionsPullbackIso_hom_ι, ← Category.assoc]
  exact _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.relativeFunctorIsPullbackForward_uncurry hs a b hab _

/-- 逆同型で持ち上げた同じ族を元の全空間へ射影すると、指定された section の族になる。 -/
lemma cocartesianSectionsPullbackIso_inv_uncurry {T : SSet.{u}}
    (k : T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianSections p b) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry ((k ≫ (cocartesianSectionsPullbackIso hs a b hab).inv) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianSectionsι r a) ≫ i =
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry (k ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianSectionsι p b) := by
  have h := cocartesianSectionsPullbackIso_hom_uncurry hs a b hab
    (k ≫ (cocartesianSectionsPullbackIso hs a b hab).inv)
  simp only [Category.assoc, Iso.inv_hom_id_assoc] at h
  exact h.symm

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
