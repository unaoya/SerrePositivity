module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.RelativeFunctorExtensionEndpoint
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.RelativeFunctorConstFiber

/-!
概要：相対延長の終点を底の一点の fiber 内の関手として取り、二つの延長を比較する。
方針：延長の包含・制限・底の等式による移送を、定値相対関手の fiber への作用に合成する。
規約：指定した終点の部分図式での底は一点に定値とする。
使われ方：Kerodon Proposition 5.2.2.8（Tag 01VS）、left fibration の射に関する transport の自然性。

対応節は Kerodon 5.2（Tag 019A）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport

/-- 概要：相対延長の空間を指定部分で評価して、終点 fiber への関手空間へ送る。
方針：相対前合成と定値相対関手から fiber への作用を合成する。
規約：j は初期値を指定する i と独立な射。
使われ方：Kerodon Proposition 5.2.2.8（Tag 01VS）、transport の終点の比較の評価射。 -/
def relativeExtensionFiberEndpoint {A D C E B : SSet.{u}}
    (p : E ⟶ B) (a : A ⟶ B) (i : D ⟶ A) (v : D ⟶ E) (hv : v ≫ p = i ≫ a)
    (j : C ⟶ A) (b : B _⦋0⦌) (hj : j ≫ a = SSet.const b) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorExtensionSpace p a i v hv ⟶
      (ihom C).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p b) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorExtensionSpaceι p a i v hv ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorPre p a j ≫
    eqToHom (congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace p) hj) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeFunctorConstFiberHom p b

/-- 概要：具体的な延長の終点が fiber への射 g なら、終点の評価は g の関手頂点。
方針：相対前合成と底の表示の移送の頂点公式を順に使う。
規約：j≫W=g≫fiber の包含を厳密な等式で指定する。
使われ方：Kerodon Proposition 5.2.2.8（Tag 01VS）、相対延長の抽象的な比較と実際の終点の接続。 -/
lemma relativeExtensionFiberEndpoint_vertex {A D C E B : SSet.{u}}
    (p : E ⟶ B) (a : A ⟶ B) (i : D ⟶ A) (v : D ⟶ E) (hv : v ≫ p = i ≫ a)
    (j : C ⟶ A) (b : B _⦋0⦌) (hj : j ≫ a = SSet.const b)
    (W : A ⟶ E) (hW : W ≫ p = a) (hWi : i ≫ W = v)
    (g : C ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p b) (hWj : j ≫ W = g ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p b) :
    (relativeExtensionFiberEndpoint p a i v hv j b hj).app _
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorExtensionSpaceVertexEquiv p a i v hv ⟨W, hW, hWi⟩) =
        _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex g := by
  have he : (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorExtensionSpaceι p a i v hv ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorPre p a j).app _
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorExtensionSpaceVertexEquiv p a i v hv ⟨W, hW, hWi⟩) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorVertex p (j ≫ a) (j ≫ W) (by rw [Category.assoc, hW]) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorPre_vertex p a j W hW
  have ht := congrArg (fun x ↦ (eqToHom (congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace p) hj)).app _ x) he
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorVertex_transport p hj (j ≫ W) (by rw [Category.assoc, hW])] at ht
  have hg : (g ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p b) ≫ p = SSet.const b := by
    rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι_comp, SSet.comp_const]
  have hvg : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorVertex p (SSet.const b) (j ≫ W)
      (by rw [Category.assoc, hW, hj]) =
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorVertex p (SSet.const b) (g ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p b) hg := by
    apply Subtype.ext
    exact congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex hWj
  exact (congrArg (fun x ↦ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeFunctorConstFiberHom (A := C) p b).app _ x) ht).trans
    ((congrArg (fun x ↦ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeFunctorConstFiberHom (A := C) p b).app _ x) hvg).trans
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeFunctorConstFiberHom_vertex p b g))

/-- 概要：共通の初期値を持つ二つの相対延長の終点は、同じ fiber 内の関手として同型。
方針：可縮な延長空間の二頂点を終点の評価射で写す。
規約：初期包含 i は left anodyne。
使われ方：Kerodon Proposition 5.2.2.8（Tag 01VS）、transport の自然性の二つの持ち上げの比較。 -/
noncomputable def relativeExtensionFiberEndpoint_witnessIso {A D C E B : SSet.{u}}
    (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] (a : A ⟶ B) (i : D ⟶ A)
    (hi : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftAnodyneExtensions i) (v : D ⟶ E) (hv : v ≫ p = i ≫ a)
    (j : C ⟶ A) (b : B _⦋0⦌) (hj : j ≫ a = SSet.const b)
    (W W' : A ⟶ E) (hW : W ≫ p = a) (hW' : W' ≫ p = a)
    (hWi : i ≫ W = v) (hWi' : i ≫ W' = v)
    (g g' : C ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p b)
    (hWj : j ≫ W = g ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p b) (hWj' : j ≫ W' = g' ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p b) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso g g' := by
  let x := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorExtensionSpaceVertexEquiv p a i v hv ⟨W, hW, hWi⟩
  let y := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorExtensionSpaceVertexEquiv p a i v hv ⟨W', hW', hWi'⟩
  have e := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map ((_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorExtensionSpace_isContractibleKan p a i hi v hv).vertexIso x y)
    (relativeExtensionFiberEndpoint p a i v hv j b hj)
  rw [relativeExtensionFiberEndpoint_vertex p a i v hv j b hj W hW hWi g hWj,
    relativeExtensionFiberEndpoint_vertex p a i v hv j b hj W' hW' hWi' g' hWj'] at e
  exact e

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport
