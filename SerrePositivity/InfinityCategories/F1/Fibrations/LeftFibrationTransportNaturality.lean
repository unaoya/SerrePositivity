module

public import SerrePositivity.InfinityCategories.F1.MappingSpaces.RelativeExtensionFiberEndpoint
public import SerrePositivity.InfinityCategories.F1.Simplicial.SimplexPrismFirstVertex
public import SerrePositivity.InfinityCategories.F1.Transport.EdgeTransport
public import SerrePositivity.InfinityCategories.F1.Transport.LeftTransport
public import SerrePositivity.InfinityCategories.Core.VertexFiberMap

/-!
概要：left fibration への底上の射は fiber 間の transport と関手同型まで可換。
方針：二つの prism の持ち上げを共通の初期値を持つ相対延長として比較する。
規約：標的が left fibration なので、全空間の射に cocartesian 辺の保存条件を追加しない。
使われ方：Kerodon Proposition 5.2.2.8、Corollary 5.6.0.6、weighted nerve と coherent な復元の transport の比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

attribute [local instance] vertexFiber_kanComplex_of_leftFibration

/-- 概要：二つの transport の証人は、left fibration への底上の射の両側で関手同型を与える。
方針：元の持ち上げへの後合成と標的の持ち上げへの前合成の初期値を揃え、終点を比較する。
規約：始域の射影 p に充填性は要求せず、指定された transport の証人を用いる。
使われ方：Kerodon Proposition 5.2.2.8、left fibration 間の比較射による輸送の自然性。 -/
noncomputable def leftFibrationTransportNaturalityIso {E E' B : SSet.{u}}
    (p : E ⟶ B) (q : E' ⟶ B) [LeftFibration q] (f : E ⟶ E') (hf : f ≫ q = p)
    {a b : B _⦋0⦌} (e : SSet.Edge a b)
    {T : vertexFiber p a ⟶ vertexFiber p b} {T' : vertexFiber q a ⟶ vertexFiber q b}
    (hT : IsEdgeTransport p e T) (hT' : IsEdgeTransport q e T') :
    FunctorIso (T ≫ vertexFiberMap p q f hf b) (vertexFiberMap p q f hf a ≫ T') := by
  let H := hT.choose
  have hH₀ := hT.choose_spec.1
  have hH₁ := hT.choose_spec.2.1
  have hHp := hT.choose_spec.2.2.1
  let K := hT'.choose
  have hK₀ := hT'.choose_spec.1
  have hK₁ := hT'.choose_spec.2.1
  have hKp := hT'.choose_spec.2.2.1
  let A := vertexFiber p a
  let β := fst (Δ[1] : SSet.{u}) A ≫ SSet.yonedaEquiv.symm e.edge
  let i := scaffoldFirstVertex 1 ▷ A
  let v := snd (Δ[0] : SSet.{u}) A ≫ vertexFiberι p a ≫ f
  let j := prismEndpoint 1 A
  let W := H ≫ f
  let W' := (Δ[1] ◁ vertexFiberMap p q f hf a) ≫ K
  have hW : W ≫ q = β := by
    dsimp only [W, β]
    rw [Category.assoc, hf, hHp]
    rfl
  have hW' : W' ≫ q = β := by
    dsimp only [W', β]
    rw [Category.assoc, hKp, ← Category.assoc, whiskerLeft_fst]
    rfl
  have hW₀ : prismEndpoint 0 A ≫ W = vertexFiberι p a ≫ f := by
    dsimp only [W]
    rw [← Category.assoc, hH₀]
  have hW₀' : prismEndpoint 0 A ≫ W' = vertexFiberι p a ≫ f := by
    dsimp only [W']
    rw [← Category.assoc, prismEndpoint_naturality, Category.assoc, hK₀, vertexFiberMap_ι]
  have hWi : i ≫ W = v := by
    dsimp only [i, v]
    rw [scaffoldFirstVertex_whiskerRight, Category.assoc]
    exact congrArg (fun z ↦ snd (Δ[0] : SSet.{u}) A ≫ z) hW₀
  have hWi' : i ≫ W' = v := by
    dsimp only [i, v]
    rw [scaffoldFirstVertex_whiskerRight, Category.assoc]
    exact congrArg (fun z ↦ snd (Δ[0] : SSet.{u}) A ≫ z) hW₀'
  have hv : v ≫ q = i ≫ β := by rw [← hWi, Category.assoc, hW]
  have hj : j ≫ β = SSet.const b :=
    (prismEdgeFamily_one e.edge).trans (congrArg (fun z ↦ (SSet.const z : A ⟶ B)) e.tgt_eq)
  have hWj : j ≫ W = (T ≫ vertexFiberMap p q f hf b) ≫ vertexFiberι q b := by
    dsimp only [j, W]
    rw [← Category.assoc, hH₁, Category.assoc, Category.assoc]
    exact congrArg (fun z ↦ T ≫ z) (vertexFiberMap_ι p q f hf b).symm
  have hWj' : j ≫ W' = (vertexFiberMap p q f hf a ≫ T') ≫ vertexFiberι q b := by
    dsimp only [j, W']
    rw [← Category.assoc, prismEndpoint_naturality, Category.assoc, hK₁, Category.assoc]
  exact relativeExtensionFiberEndpoint_witnessIso q β i
    (simplexPrismFirstVertex_leftAnodyne 1 A) v hv j b hj W W' hW hW' hWi hWi'
    (T ≫ vertexFiberMap p q f hf b) (vertexFiberMap p q f hf a ≫ T') hWj hWj'

/-- 概要：left fibrations 間の底上の射は標準 transport と関手同型まで可換。
方針：標準 transport の二つの持ち上げの証人に自然性の比較を適用する。
規約：比較の両辺は始域の始点 fiber から標的の終点 fiber への射。
使われ方：Kerodon Corollary 5.6.0.6、復元の全空間比較から fiber 間の作用を比較する。 -/
noncomputable def leftFibrationMap_transportIso {E E' B : SSet.{u}}
    (p : E ⟶ B) (q : E' ⟶ B) [LeftFibration p] [LeftFibration q]
    (f : E ⟶ E') (hf : f ≫ q = p) {a b : B _⦋0⦌} (e : SSet.Edge a b) :
    FunctorIso
      (edgeTransport p e ≫ vertexFiberMap p q f hf b)
      (vertexFiberMap p q f hf a ≫ edgeTransport q e) :=
  leftFibrationTransportNaturalityIso p q f hf e (edgeTransport_isTransport p e)
    (edgeTransport_isTransport q e)

/-- 概要：始点と終点の fiber で同値な底上の射は transport の同値性を保存・反映する。
方針：transport の自然性の関手同型と fiber 射の同値性に二対三則を使う。
規約：底 B 自体の quasicategory 性は不要。
使われ方：Kerodon Corollary 5.6.0.6、weighted nerve と unstraightening の比較で射の同値性を検出する。 -/
lemma leftFibrationMap_transport_isQCatEquivalence_iff {E E' B : SSet.{u}}
    (p : E ⟶ B) (q : E' ⟶ B) [LeftFibration p] [LeftFibration q]
    (f : E ⟶ E') (hf : f ≫ q = p) {a b : B _⦋0⦌} (e : SSet.Edge a b)
    (ha : IsQCatEquivalence (vertexFiberMap p q f hf a))
    (hb : IsQCatEquivalence (vertexFiberMap p q f hf b)) :
    IsQCatEquivalence (edgeTransport p e) ↔ IsQCatEquivalence (edgeTransport q e) := by
  have h := leftFibrationMap_transportIso p q f hf e
  constructor
  · intro he
    exact ha.cancel_left ((he.comp hb).ofFunctorIso h)
  · intro he
    exact hb.cancel_right ((ha.comp he).ofFunctorIso h.symm)

end SerrePositivity.InfinityCategories
