module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.GrothendieckConstruction.UniverseIntervalHom
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.KanComparisonFibers

/-!
概要：Kan 複体の可逆 path と ULift の標準同型と両端評価・後合成の厳密な整合性。
方針：Kan 複体の全ての path が可逆なことを使って通常の区間関手空間の同型へ移す。
規約：同型は path の向きと端点の番号を保持する。
使われ方：HTT 4.2.4.1、導来 fiber の ULift と元の q_x の固定点の比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
noncomputable section

/-- 概要：Kan 複体の可逆 path の ULift は持ち上げた複体の可逆 path と厳密に同型。
方針：両側の可逆 path の包含の同型と区間関手空間の ULift の同型を合成する。
規約：元の複体の Kan 性だけを要求する。
使われ方：元の比較射の path 置換の宇宙の移送。 -/
def uliftEquivalencePathIso (B : SSet.{u}) [KanComplex B] :
    (SSet.uliftFunctor.{v, u}).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePath B) ≅
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePath ((SSet.uliftFunctor.{v, u}).obj B) :=
  (SSet.uliftFunctor.{v, u}).mapIso (asIso (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathι B)) ≪≫
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.uliftIntervalHomIso B ≪≫ (asIso (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathι ((SSet.uliftFunctor.{v, u}).obj B))).symm

/-- 概要：可逆 path の ULift の同型は通常の区間関手空間への包含と厳密に可換。
方針：最後の同型の逆射と包含を消去する。
規約：同型の順射について述べる。
使われ方：端点評価と後合成の可換式の確認。 -/
lemma uliftEquivalencePathIso_hom_ι (B : SSet.{u}) [KanComplex B] :
    (uliftEquivalencePathIso.{u, v} B).hom ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathι ((SSet.uliftFunctor.{v, u}).obj B) =
      (SSet.uliftFunctor.{v, u}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathι B) ≫
        (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.uliftIntervalHomIso.{u, v} B).hom := by
  simp only [uliftEquivalencePathIso, Iso.trans_hom, Iso.symm_hom, asIso_inv,
    CategoryTheory.Functor.mapIso_hom, asIso_hom,
    Category.assoc, IsIso.inv_hom_id, Category.comp_id]

/-- 概要：可逆 path の ULift の標準同型は両端点の評価と厳密に可換。
方針：包含の可換式と通常の区間関手空間の端点評価を組み合わせる。
規約：始点 j=0 と終点 j=1 を同じ式で扱う。
使われ方：導来 fiber の始点条件と固定する終点の保持。 -/
lemma uliftEquivalencePathIso_hom_endpoint (B : SSet.{u}) [KanComplex B] (j : Fin 2) :
    (uliftEquivalencePathIso.{u, v} B).hom ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint ((SSet.uliftFunctor.{v, u}).obj B) j =
      (SSet.uliftFunctor.{v, u}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint B j) := by
  change _ ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathι _ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt _) = _
  rw [← Category.assoc, uliftEquivalencePathIso_hom_ι, Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.uliftIntervalHomIso_hom_evaluate, ← CategoryTheory.Functor.map_comp]
  rfl

/-- 概要：可逆 path の ULift の標準同型は path の後合成と厳密に可換。
方針：包含後で消去し、通常の区間関手空間の比較の自然性へ帰着する。
規約：両端の Kan 性を要求するが元の射の fibration 性は不要。
使われ方：path 置換とその源・終点射影の宇宙の移送。 -/
lemma uliftEquivalencePathIso_hom_naturality {E B : SSet.{u}} [KanComplex E] [KanComplex B]
    (p : E ⟶ B) :
    (uliftEquivalencePathIso.{u, v} E).hom ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathMap ((SSet.uliftFunctor.{v, u}).map p) =
      (SSet.uliftFunctor.{v, u}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathMap p) ≫
        (uliftEquivalencePathIso.{u, v} B).hom := by
  apply (cancel_mono (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathι ((SSet.uliftFunctor.{v, u}).obj B))).1
  simp only [Category.assoc]
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathMap_ι, ← Category.assoc, uliftEquivalencePathIso_hom_ι,
    Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.uliftIntervalHomIso_hom_naturality, ← Category.assoc,
    ← CategoryTheory.Functor.map_comp, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathMap_ι,
    CategoryTheory.Functor.map_comp, Category.assoc, uliftEquivalencePathIso_hom_ι]

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
