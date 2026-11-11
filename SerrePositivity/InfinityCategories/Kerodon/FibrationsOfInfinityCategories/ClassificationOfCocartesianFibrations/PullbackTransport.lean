module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftUnstraighteningFiberIso
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.EdgeTransport
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.LeftTransport
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftUnstraighteningFiberKan
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PrecompositionTensor

/-!
概要：left fibration の transport と底の引き戻しの整合性。
方針：引き戻し内の prism を第一射影で写し、標準 fiber 同型で両端を移す。
規約：底の quasicategory 性は要求しない。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、普遍 left fibration の作用を図式の復元と比較する。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

attribute [local instance] _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_kanComplex_of_leftFibration

/-- 概要：left fibration の引き戻しの第二射影は left fibration。
方針：left anodyne 射に関する右持ち上げ性の引き戻し安定性を使う。
規約：第一引数を引き戻す射、第二引数を底の変更とする。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、引き戻しの transport の構成。 -/
instance leftFibration_pullback_snd {E B C : SSet.{u}} (p : E ⟶ B) (k : C ⟶ B)
    [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration (pullback.snd p k) :=
  ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrations.pullback_snd p k (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration.mem (p := p))⟩

/-- 概要：fiber 同型の逆を全空間へ含めて第一射影で写すと元の fiber の包含になる。
方針：順方向の包含公式の左に同型の逆を合成する。
規約：式は元の全空間 E への射の等式。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、引き戻した transport の始点条件。 -/
lemma vertexFiberPullbackIso_inv_ι_fst {E B C : SSet.{u}}
    (p : E ⟶ B) (k : C ⟶ B) (a : C _⦋0⦌) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.vertexFiberPullbackIso p k a).inv ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (pullback.snd p k) a ≫
      pullback.fst p k = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p (k.app (Opposite.op ⦋0⦌) a) := by
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.vertexFiberPullbackIso_hom_ι, Iso.inv_hom_id_assoc]

/-- 概要：引き戻しの transport の証人は fiber 同型を介して元の射影の証人を与える。
方針：始点 fiber の同型の逆で prism を制限し、第一射影で写す。
規約：元の底の辺は k による e の像。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、普遍射影の輸送と unstraightening の輸送の比較。 -/
lemma IsEdgeTransport.pullback {E B C : SSet.{u}}
    (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] (k : C ⟶ B)
    {a b : C _⦋0⦌} (e : SSet.Edge a b)
    {T : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (pullback.snd p k) a ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (pullback.snd p k) b}
    (hT : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.IsEdgeTransport (pullback.snd p k) e T) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.IsEdgeTransport p (e.map k)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.vertexFiberPullbackIso p k a).inv ≫ T ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.vertexFiberPullbackIso p k b).hom) := by
  obtain ⟨H, hH₀, hH₁, hHp, _⟩ := hT
  refine ⟨(Δ[1] ◁ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.vertexFiberPullbackIso p k a).inv) ≫ H ≫ pullback.fst p k,
    ?_, ?_, ?_, fun _ ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.isCocartesianEdge_of_leftFibration _ _⟩
  · rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint_naturality, Category.assoc,
      ← Category.assoc (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 _),
      hH₀, vertexFiberPullbackIso_inv_ι_fst]
  · rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint_naturality, Category.assoc,
      ← Category.assoc (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 _),
      hH₁]
    simp only [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.vertexFiberPullbackIso_hom_ι]
  · rw [Category.assoc, Category.assoc, pullback.condition, ← Category.assoc H, hHp,
      ← Category.assoc, ← Category.assoc, whiskerLeft_fst, Category.assoc]
    congr 1
    exact SSet.yonedaEquiv_symm_comp _ k

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.IsEdgeTransport export _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.IsEdgeTransport (pullback)


/-- 概要：引き戻しの標準 transport は fiber 同型で移すと像の辺の標準 transport と関手同型。
方針：引き戻しの証人を移した後、left fibration の transport の一意性を適用する。
規約：同型は元の終点 fiber 内で取る。
使われ方：Kerodon Proposition 5.2.2.8（Tag 01VS）、Corollary 5.6.0.6（Tag 028T）、底の変更と選択した輸送の整合性。 -/
noncomputable def edgeTransport_pullbackIso {E B C : SSet.{u}}
    (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] (k : C ⟶ B)
    {a b : C _⦋0⦌} (e : SSet.Edge a b) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.vertexFiberPullbackIso p k a).inv ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.edgeTransport (pullback.snd p k) e ≫
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.vertexFiberPullbackIso p k b).hom)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.edgeTransport p (e.map k)) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.IsEdgeTransport.functorIso p (e.map k)
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.edgeTransport_isTransport (pullback.snd p k) e).pullback p k e)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.edgeTransport_isTransport p (e.map k))).some

/-- 概要：引き戻した辺の transport の同値性は、元の底の像の辺の transport の同値性と一致する。
方針：transport の関手同型と、両端の fiber 同型に同値の二対三則を使う。
規約：同値性は Kan fiber 間の quasicategory 同値として述べる。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、普遍射影の作用の同値性を図式の復元から判定する。 -/
lemma edgeTransport_pullback_isQCatEquivalence_iff {E B C : SSet.{u}}
    (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] (k : C ⟶ B)
    {a b : C _⦋0⦌} (e : SSet.Edge a b) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.edgeTransport (pullback.snd p k) e) ↔
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.edgeTransport p (e.map k)) := by
  have ha := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.vertexFiberPullbackIso p k a).symm).isQCatEquivalence
  have hb := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.vertexFiberPullbackIso p k b)).isQCatEquivalence
  have h := edgeTransport_pullbackIso p k e
  constructor
  · intro he
    exact (ha.comp (he.comp hb)).ofFunctorIso h
  · intro he
    exact ha.cancel_left (hb.cancel_right (he.ofFunctorIso h.symm))

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
