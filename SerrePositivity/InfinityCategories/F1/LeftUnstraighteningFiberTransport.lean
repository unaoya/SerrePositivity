module

public import SerrePositivity.InfinityCategories.F1.LeftUnstraighteningSelectedLift
public import SerrePositivity.InfinityCategories.F1.LeftUnstraighteningFunctorEdge
public import SerrePositivity.InfinityCategories.F1.FunctorPrismFiber
public import SerrePositivity.InfinityCategories.F1.LeftUnstraighteningFiberIso
public import SerrePositivity.InfinityCategories.F1.EdgeTransport
public import SerrePositivity.InfinityCategories.Core.VertexFiberMap

/-!
概要：unstraightening の辺への作用を pointed-space 射影の fiber 間の transport として表示する。
方針：選択した変換の具体的な持ち上げを底の fiber へ制限する。
規約：fiber の同型で比較し、空間値の Kan 複体との同値はまだ合成しない。
使われ方：Kerodon Corollary 5.6.0.6、選択済みの写像空間比較と空間値での作用の接続。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：unstraightening の fiber 同型の順方向を pointed space に含めると第一射影になる。
方針：引き戻しの fiber 同型の計算則を適用する。
規約：底の任意の頂点 b を固定する。
使われ方：Kerodon Example 5.6.2.9、fiber 上の射の pointed space 成分の計算。 -/
lemma leftUnstraighteningFiberIso_hom_ι {B : SSet.{u + 1}}
    (F : B ⟶ SpaceInfinity.{u}) (b : B _⦋0⦌) :
    (leftUnstraighteningFiberIso F b).hom ≫
      vertexFiberι pointedSpaceProjection (F.app _ b) =
    vertexFiberι (leftUnstraighteningProjection F) b ≫ pullback.fst pointedSpaceProjection F :=
  vertexFiberPullbackIso_hom_ι pointedSpaceProjection F b

/-- 概要：fiber 同型の逆射で unstraightening に戻し第一射影を取ると元の fiber の包含。
方針：順方向の計算式に逆射を前合成して同型の往復を消去する。
規約：元の pointed-space fiber の始点を厳密に保つ式。
使われ方：Kerodon Example 5.6.2.9、prism を fiber に制限した持ち上げの初期値。 -/
lemma leftUnstraighteningFiberIso_inv_ι_fst {B : SSet.{u + 1}}
    (F : B ⟶ SpaceInfinity.{u}) (b : B _⦋0⦌) :
    (leftUnstraighteningFiberIso F b).inv ≫
      vertexFiberι (leftUnstraighteningProjection F) b ≫ pullback.fst pointedSpaceProjection F =
    vertexFiberι pointedSpaceProjection (F.app _ b) := by
  rw [← leftUnstraighteningFiberIso_hom_ι, Iso.inv_hom_id_assoc]

/-- 概要：底上の unstraightening の射を対応する pointed-space fiber 間の射にする。
方針：通常の fiber 射の両側に fiber の引き戻し同型を合成する。
規約：始点・終点は図式の頂点での値を添字に持つ fiber。
使われ方：Kerodon Corollary 5.6.0.6、変換の作用の値での比較。 -/
noncomputable def leftUnstraighteningPointedFiberMap {B : SSet.{u + 1}}
    (F G : B ⟶ SpaceInfinity.{u}) (f : leftUnstraightening F ⟶ leftUnstraightening G)
    (hf : f ≫ leftUnstraighteningProjection G = leftUnstraighteningProjection F)
    (b : B _⦋0⦌) :
    vertexFiber pointedSpaceProjection (F.app _ b) ⟶
      vertexFiber pointedSpaceProjection (G.app _ b) :=
  (leftUnstraighteningFiberIso F b).inv ≫
    vertexFiberMap (leftUnstraighteningProjection F) (leftUnstraighteningProjection G) f hf b ≫
      (leftUnstraighteningFiberIso G b).hom

/-- 概要：pointed-space fiber 間の射の包含は元の全空間の射と第一射影の合成。
方針：fiber 同型と通常の fiber 射の包含の計算則を使う。
規約：始域の fiber 同型の逆射を前合成したまま保持する。
使われ方：Kerodon Corollary 5.6.0.6、選択した変換の持ち上げの終点の同定。 -/
lemma leftUnstraighteningPointedFiberMap_ι {B : SSet.{u + 1}}
    (F G : B ⟶ SpaceInfinity.{u}) (f : leftUnstraightening F ⟶ leftUnstraightening G)
    (hf : f ≫ leftUnstraighteningProjection G = leftUnstraighteningProjection F)
    (b : B _⦋0⦌) :
    leftUnstraighteningPointedFiberMap F G f hf b ≫
      vertexFiberι pointedSpaceProjection (G.app _ b) =
    (leftUnstraighteningFiberIso F b).inv ≫
      vertexFiberι (leftUnstraighteningProjection F) b ≫ f ≫
        pullback.fst pointedSpaceProjection G := by
  rw [leftUnstraighteningPointedFiberMap, Category.assoc, Category.assoc,
    leftUnstraighteningFiberIso_hom_ι]
  have h := vertexFiberMap_ι (leftUnstraighteningProjection F)
    (leftUnstraighteningProjection G) f hf b
  exact congrArg (fun z ↦ (leftUnstraighteningFiberIso F b).inv ≫ z ≫
    pullback.fst pointedSpaceProjection G) h

/-- 概要：選択済み unstraightening の辺への作用は各 fiber で pointed-space 射影の transport。
方針：選択した変換の prism の持ち上げを、引き戻しの fiber 同型で始域 fiber へ制限する。
規約：coherent な変換 e は任意であり、底や辺の可逆性は要求しない。
使われ方：Kerodon Corollary 5.6.0.6、選択済みの比較射を空間値の作用と照合する基礎。 -/
lemma leftUnstraighteningEdgeMap_pointedFiber_isTransport {B : SSet.{u + 1}}
    (F G : B ⟶ SpaceInfinity.{u})
    (e : SSet.Edge (X := (ihom B).obj SpaceInfinity.{u})
      (functorVertex F) (functorVertex G)) (b : B _⦋0⦌) :
    IsEdgeTransport pointedSpaceProjection (functorEdgeAt e b)
      (leftUnstraighteningPointedFiberMap F G (leftUnstraighteningEdgeMap F G e).val
        (leftUnstraighteningEdgeMap F G e).property b) := by
  obtain ⟨W, hW₀, hW₁, hWp⟩ := exists_leftUnstraighteningTransformationMap_lift F G
    (functorEdgePrism e) (functorEdgePrism_zero e) (functorEdgePrism_one e)
  change prismEndpoint 1 _ ≫ W =
    (leftUnstraighteningEdgeMap F G e).val ≫ pullback.fst pointedSpaceProjection G at hW₁
  let i := (leftUnstraighteningFiberIso F b).inv ≫
    vertexFiberι (leftUnstraighteningProjection F) b
  let H := (Δ[1] ◁ i) ≫ W
  refine ⟨H, ?_, ?_, ?_, fun _ ↦ isCocartesianEdge_of_leftFibration pointedSpaceProjection _⟩
  · dsimp only [H]
    rw [← Category.assoc, prismEndpoint_naturality, Category.assoc, hW₀]
    exact leftUnstraighteningFiberIso_inv_ι_fst F b
  · dsimp only [H]
    rw [← Category.assoc, prismEndpoint_naturality, Category.assoc, hW₁]
    exact (leftUnstraighteningPointedFiberMap_ι F G (leftUnstraighteningEdgeMap F G e).val
      (leftUnstraighteningEdgeMap F G e).property b).symm
  · have hi : i ≫ leftUnstraighteningProjection F = SSet.const b := by
      dsimp only [i]
      rw [Category.assoc, vertexFiberι_comp, SSet.comp_const]
    change ((Δ[1] ◁ i) ≫ W) ≫ pointedSpaceProjection =
      fst _ _ ≫ SSet.yonedaEquiv.symm (e.map (evaluateFunctorAt b)).edge
    rw [Category.assoc, hWp, ← Category.assoc, ← MonoidalCategory.whiskerLeft_comp,
      hi, functorEdgePrism_const]

/-- 概要：unstraightening の fiber 上の作用は、評価した辺に沿って選択した標準 transport と関手同型。
方針：具体的な持ち上げから得た transport と F1b の標準 transport の一意性を使う。
規約：同型は pointed-space の終点 fiber に値を持つ関手の間で取る。
使われ方：Kerodon Proposition 5.2.2.8、Corollary 5.6.0.6、変換の作用と transport の接続。 -/
noncomputable def leftUnstraighteningEdgeMap_pointedFiberTransportIso {B : SSet.{u + 1}}
    (F G : B ⟶ SpaceInfinity.{u})
    (e : SSet.Edge (X := (ihom B).obj SpaceInfinity.{u})
      (functorVertex F) (functorVertex G)) (b : B _⦋0⦌) :
    FunctorIso
      (leftUnstraighteningPointedFiberMap F G (leftUnstraighteningEdgeMap F G e).val
        (leftUnstraighteningEdgeMap F G e).property b)
      (edgeTransport pointedSpaceProjection (functorEdgeAt e b)) :=
  (IsEdgeTransport.functorIso pointedSpaceProjection (functorEdgeAt e b)
    (leftUnstraighteningEdgeMap_pointedFiber_isTransport F G e b)
    (edgeTransport_isTransport pointedSpaceProjection (functorEdgeAt e b))).some

end SerrePositivity.InfinityCategories
