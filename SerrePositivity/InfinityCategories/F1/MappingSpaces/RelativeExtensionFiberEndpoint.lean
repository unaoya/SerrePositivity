module

public import SerrePositivity.InfinityCategories.F1.FunctorCategories.RelativeFunctorExtensionEndpoint
public import SerrePositivity.InfinityCategories.F1.FunctorCategories.RelativeFunctorConstFiber

/-!
概要：相対延長の終点を底の一点の fiber 内の関手として取り、二つの延長を比較する。
方針：延長の包含・制限・底の等式による移送を、定値相対関手の fiber への作用に合成する。
規約：指定した終点の部分図式での底は一点に定値とする。
使われ方：Kerodon Proposition 5.2.2.8、left fibration の射に関する transport の自然性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：相対延長の空間を指定部分で評価して、終点 fiber への関手空間へ送る。
方針：相対前合成と定値相対関手から fiber への作用を合成する。
規約：j は初期値を指定する i と独立な射。
使われ方：Kerodon Proposition 5.2.2.8、transport の終点の比較の評価射。 -/
def relativeExtensionFiberEndpoint {A D C E B : SSet.{u}}
    (p : E ⟶ B) (a : A ⟶ B) (i : D ⟶ A) (v : D ⟶ E) (hv : v ≫ p = i ≫ a)
    (j : C ⟶ A) (b : B _⦋0⦌) (hj : j ≫ a = SSet.const b) :
    relativeFunctorExtensionSpace p a i v hv ⟶
      (ihom C).obj (vertexFiber p b) :=
  relativeFunctorExtensionSpaceι p a i v hv ≫ relativeFunctorPre p a j ≫
    eqToHom (congrArg (relativeFunctorSpace p) hj) ≫ relativeFunctorConstFiberHom p b

/-- 概要：具体的な延長の終点が fiber への射 g なら、終点の評価は g の関手頂点。
方針：相対前合成と底の表示の移送の頂点公式を順に使う。
規約：j≫W=g≫fiber の包含を厳密な等式で指定する。
使われ方：Kerodon Proposition 5.2.2.8、相対延長の抽象的な比較と実際の終点の接続。 -/
lemma relativeExtensionFiberEndpoint_vertex {A D C E B : SSet.{u}}
    (p : E ⟶ B) (a : A ⟶ B) (i : D ⟶ A) (v : D ⟶ E) (hv : v ≫ p = i ≫ a)
    (j : C ⟶ A) (b : B _⦋0⦌) (hj : j ≫ a = SSet.const b)
    (W : A ⟶ E) (hW : W ≫ p = a) (hWi : i ≫ W = v)
    (g : C ⟶ vertexFiber p b) (hWj : j ≫ W = g ≫ vertexFiberι p b) :
    (relativeExtensionFiberEndpoint p a i v hv j b hj).app _
      (relativeFunctorExtensionSpaceVertexEquiv p a i v hv ⟨W, hW, hWi⟩) =
        functorVertex g := by
  have he : (relativeFunctorExtensionSpaceι p a i v hv ≫ relativeFunctorPre p a j).app _
      (relativeFunctorExtensionSpaceVertexEquiv p a i v hv ⟨W, hW, hWi⟩) =
      relativeFunctorVertex p (j ≫ a) (j ≫ W) (by rw [Category.assoc, hW]) :=
    relativeFunctorPre_vertex p a j W hW
  have ht := congrArg (fun x ↦ (eqToHom (congrArg (relativeFunctorSpace p) hj)).app _ x) he
  rw [relativeFunctorVertex_transport p hj (j ≫ W) (by rw [Category.assoc, hW])] at ht
  have hg : (g ≫ vertexFiberι p b) ≫ p = SSet.const b := by
    rw [Category.assoc, vertexFiberι_comp, SSet.comp_const]
  have hvg : relativeFunctorVertex p (SSet.const b) (j ≫ W)
      (by rw [Category.assoc, hW, hj]) =
        relativeFunctorVertex p (SSet.const b) (g ≫ vertexFiberι p b) hg := by
    apply Subtype.ext
    exact congrArg functorVertex hWj
  exact (congrArg (fun x ↦ (relativeFunctorConstFiberHom (A := C) p b).app _ x) ht).trans
    ((congrArg (fun x ↦ (relativeFunctorConstFiberHom (A := C) p b).app _ x) hvg).trans
      (relativeFunctorConstFiberHom_vertex p b g))

/-- 概要：共通の初期値を持つ二つの相対延長の終点は、同じ fiber 内の関手として同型。
方針：可縮な延長空間の二頂点を終点の評価射で写す。
規約：初期包含 i は left anodyne。
使われ方：Kerodon Proposition 5.2.2.8、transport の自然性の二つの持ち上げの比較。 -/
noncomputable def relativeExtensionFiberEndpoint_witnessIso {A D C E B : SSet.{u}}
    (p : E ⟶ B) [LeftFibration p] (a : A ⟶ B) (i : D ⟶ A)
    (hi : leftAnodyneExtensions i) (v : D ⟶ E) (hv : v ≫ p = i ≫ a)
    (j : C ⟶ A) (b : B _⦋0⦌) (hj : j ≫ a = SSet.const b)
    (W W' : A ⟶ E) (hW : W ≫ p = a) (hW' : W' ≫ p = a)
    (hWi : i ≫ W = v) (hWi' : i ≫ W' = v)
    (g g' : C ⟶ vertexFiber p b)
    (hWj : j ≫ W = g ≫ vertexFiberι p b) (hWj' : j ≫ W' = g' ≫ vertexFiberι p b) :
    FunctorIso g g' := by
  let x := relativeFunctorExtensionSpaceVertexEquiv p a i v hv ⟨W, hW, hWi⟩
  let y := relativeFunctorExtensionSpaceVertexEquiv p a i v hv ⟨W', hW', hWi'⟩
  have e := VertexIso.map ((relativeFunctorExtensionSpace_isContractibleKan p a i hi v hv).vertexIso x y)
    (relativeExtensionFiberEndpoint p a i v hv j b hj)
  rw [relativeExtensionFiberEndpoint_vertex p a i v hv j b hj W hW hWi g hWj,
    relativeExtensionFiberEndpoint_vertex p a i v hv j b hj W' hW' hWi' g' hWj'] at e
  exact e

end SerrePositivity.InfinityCategories
