module

public import SerrePositivity.InfinityCategories.HomotopyLimits.RelativeFunctorPostcomposition

/-!
概要：底を保つ全空間の射は strict transport の図式の自然変換を与える。
方針：各 under 圏上で相対関手を後合成し、恒等射での評価との可換性で同値性を検出する。
規約：全空間の比較は実際の射 f とその底を保つ等式で指定する。
使われ方：Kerodon 5.3.1.5、7.4.1.6、7.5.4.6 の coherent な錐の模型の比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.HomotopyLimits
variable {I : Type u} [SmallCategory I] {E E' : SSet.{u}}

/-- 概要：strict transport の図式の対象表示でも Kan 性を型クラスとして使える。
方針：under 圏の相対関手空間の既存の Kan 性を図式の値として表示する。
規約：底への射影 p は left fibration。
使われ方：Kerodon 5.3.1.5 の図式の成分ごとの同値の判定。 -/
instance strictTransportDiagram_kanComplex (p : E ⟶ nerve I) [LeftFibration p] (i : I) :
    KanComplex ((leftStrictTransportDiagram p).obj i) := leftStrictTransport_kanComplex p i

/-- 概要：底を保つ全空間の射が strict transport の自然変換を誘導する。
方針：各 under 圏の相対関手空間で後合成し、前合成との可換性を自然性に使う。
規約：定義には left fibration 性は要求しない。
使われ方：Kerodon 5.3.1.5、7.5.4.6 の係数図式の全体の比較。 -/
def strictTransportPost (p : E ⟶ nerve I) (q : E' ⟶ nerve I)
    (f : E ⟶ E') (hf : f ≫ q = p) :
    leftStrictTransportDiagram p ⟶ leftStrictTransportDiagram q where
  app i := relativeFunctorPost p q f hf (nerveMap (Under.forget i))
  naturality i _j r :=
    (relativeFunctorPost_pre p q f hf (nerveMap (Under.forget i)) (nerveUnderMap r)).symm

/-- 概要：transport の全空間の比較は恒等射での評価を介して元の fiber の比較と可換。
方針：fiber の包含後に後合成と内部 Hom の頂点評価を交換する。
規約：図式の対象 i は任意。
使われ方：Kerodon 5.3.1.5 の fiber ごとの同値から図式の成分ごとの同値への移送。 -/
lemma strictTransportPost_evaluate (p : E ⟶ nerve I) (q : E' ⟶ nerve I)
    (f : E ⟶ E') (hf : f ≫ q = p) (i : I) :
    (strictTransportPost p q f hf).app i ≫ leftStrictTransportEvaluate q i =
      leftStrictTransportEvaluate p i ≫
        vertexFiberMap p q f hf ((nerveEquiv (C := I)).symm i) := by
  apply vertexFiber_hom_ext q ((nerveEquiv (C := I)).symm i)
  change (vertexFiberι ((ihom (nerve (Under i))).map p)
      (functorVertex (nerveMap (Under.forget i))) ≫ (ihom (nerve (Under i))).map f) ≫
        evaluateFunctorAt (strictTransportUnderIdentityVertex i) =
    (vertexFiberι ((ihom (nerve (Under i))).map p)
      (functorVertex (nerveMap (Under.forget i))) ≫
        evaluateFunctorAt (strictTransportUnderIdentityVertex i)) ≫ f
  rw [Category.assoc, Category.assoc]
  rfl

/-- 概要：left fibration 間の底を保つ射の各 fiber が同値なら transport の各成分も同値。
方針：両側の恒等射評価の同値性と fiber 比較との可換性を二対三で使う。
規約：対象 i での fiber の同値性だけを要求する。
使われ方：Kerodon 5.3.1.5、7.5.4.6 の全空間の比較から end の比較への橋渡し。 -/
lemma strictTransportPost_component_isQCatEquivalence
    (p : E ⟶ nerve I) (q : E' ⟶ nerve I) [LeftFibration p] [LeftFibration q]
    (f : E ⟶ E') (hf : f ≫ q = p) (i : I)
    (hi : IsQCatEquivalence (vertexFiberMap p q f hf ((nerveEquiv (C := I)).symm i))) :
    IsQCatEquivalence ((strictTransportPost p q f hf).app i :
      leftStrictTransport p i ⟶ leftStrictTransport q i) := by
  apply (leftStrictTransportEvaluate_isQCatEquivalence q i).cancel_right
  rw [strictTransportPost_evaluate]
  exact (leftStrictTransportEvaluate_isQCatEquivalence p i).comp hi

/-- 概要：left fibration 間の fiber ごとの同値は transport の end 全体のホモトピー同値を誘導する。
方針：恒等射評価で成分ごとの同値を検出し、Bousfield–Kan end の同値不変性を適用する。
規約：底は任意の小圏の nerve でよく、遷移の fibration 性は不要。
使われ方：Kerodon 7.4.1.6、7.5.4.6 の coherent な錐の模型の比較の大域化。 -/
lemma strictTransportPost_end_homotopyEquivalence
    (p : E ⟶ nerve I) (q : E' ⟶ nerve I) [LeftFibration p] [LeftFibration q]
    (f : E ⟶ E') (hf : f ≫ q = p)
    (h : ∀ i, IsQCatEquivalence (vertexFiberMap p q f hf ((nerveEquiv (C := I)).symm i))) :
    IsSimplicialHomotopyEquivalence
      (weightedSectionsMap (bousfieldKanWeight I) (strictTransportPost p q f hf)) := by
  have (i : I) : KanComplex ((leftStrictTransportDiagram p).obj i) :=
    leftStrictTransport_kanComplex p i
  have (i : I) : KanComplex ((leftStrictTransportDiagram q).obj i) :=
    leftStrictTransport_kanComplex q i
  have he := bousfieldKanMap_isQCatEquivalence (strictTransportPost p q f hf)
    (fun i ↦ strictTransportPost_component_isQCatEquivalence p q f hf i (h i))
  exact he.isSimplicialHomotopyEquivalence

end SerrePositivity.InfinityCategories.HomotopyLimits
