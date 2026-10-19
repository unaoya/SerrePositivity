module

public import SerrePositivity.InfinityCategories.F1.TransportSquareFunctor
public import SerrePositivity.InfinityCategories.F1.TransportSquareRepresentationRestriction
public import SerrePositivity.InfinityCategories.F1.VertexFiberTotalIso

/-!
概要：pullback 正方形の前合成は各 fiber の同型を通して表現条件を保つ。
方針：標準の pullback への同型と pullback fiber の同型を続ける。
規約：底の射の同値性や単射性は不要。
使われ方：底上の射の図式で実際の表現空間を関手に束ねる。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

attribute [local instance] vertexFiber_kanComplex_of_leftFibration

/-- 概要：pullback 正方形の各 fiber は底の像の元の fiber と同型。
方針：全空間を標準の pullback へ移し、pullback の fiber を回収する。
規約：射影の充填性は不要。
使われ方：表現条件の底変換による保存と反映。 -/
def transportCartesianSquareFiberIso {p q : Arrow SSet.{u}} (f : p ⟶ q)
    (hf : IsPullback f.left p.hom q.hom f.right) (b : p.right _⦋0⦌) :
    vertexFiber p.hom b ≅ vertexFiber q.hom (f.right.app _ b) :=
  vertexFiberTotalIso p.hom (pullback.snd q.hom f.right) hf.isoPullback
    hf.isoPullback_hom_snd b ≪≫ vertexFiberPullbackIso q.hom f.right b

/-- 概要：pullback 正方形の fiber 同型は全空間の射を厳密に回収する。
方針：二つの標準 fiber 同型の包含公式を計算する。
規約：全高次単体の射の等式。
使われ方：pointed space の fiber 比較の可換性。 -/
lemma transportCartesianSquareFiberIso_hom_ι {p q : Arrow SSet.{u}} (f : p ⟶ q)
    (hf : IsPullback f.left p.hom q.hom f.right) (b : p.right _⦋0⦌) :
    (transportCartesianSquareFiberIso f hf b).hom ≫ vertexFiberι q.hom (f.right.app _ b) =
      vertexFiberι p.hom b ≫ f.left := by
  dsimp only [transportCartesianSquareFiberIso, Iso.trans_hom]
  rw [Category.assoc, vertexFiberPullbackIso_hom_ι, ← Category.assoc]
  change (vertexFiberMap p.hom (pullback.snd q.hom f.right) hf.isoPullback.hom
    hf.isoPullback_hom_snd b ≫ vertexFiberι (pullback.snd q.hom f.right) b) ≫
      pullback.fst q.hom f.right = _
  rw [vertexFiberMap_ι, Category.assoc, hf.isoPullback_hom_fst]

/-- 概要：pullback 正方形による前合成の fiber 比較は標準 fiber 同型に沿う前合成。
方針：普遍 pointed-space fiber の包含後に両辺を比較する。
規約：分類図式を像の頂点で厳密に評価する。
使われ方：表現条件の頂点ごとの判定。 -/
lemma LeftTransportSquare.preSquare_pointedFiberMap {p q : Arrow SSet.{u + 1}}
    (S : LeftTransportSquare q.hom) (f : p ⟶ q)
    (hf : IsPullback f.left p.hom q.hom f.right) (b : p.right _⦋0⦌) :
    (S.preSquare f).pointedFiberMap b =
      (transportCartesianSquareFiberIso f hf b).hom ≫ S.pointedFiberMap (f.right.app _ b) := by
  apply vertexFiber_hom_ext pointedSpaceProjection (S.diagram.app _ (f.right.app _ b))
  have hS : (S.preSquare f).pointedFiberMap b ≫
      vertexFiberι pointedSpaceProjection (S.diagram.app _ (f.right.app _ b)) =
      vertexFiberι p.hom b ≫ (f.left ≫ S.pointedMap) := (S.preSquare f).pointedFiberMap_ι b
  rw [hS, Category.assoc, S.pointedFiberMap_ι]
  simp only [← Category.assoc]
  rw [transportCartesianSquareFiberIso_hom_ι]

/-- 概要：pullback 正方形による前合成の表現条件は底の像の頂点の条件と同値。
方針：fiber 同型を二対三則で消去する。
規約：各射影は left fibration。
使われ方：余極限の全頂点を被覆する脚で表現条件を判定する。 -/
lemma LeftTransportSquare.preSquare_pointedFiberMap_isQCatEquivalence_iff
    {p q : Arrow SSet.{u + 1}} [LeftFibration p.hom] [LeftFibration q.hom]
    (S : LeftTransportSquare q.hom) (f : p ⟶ q)
    (hf : IsPullback f.left p.hom q.hom f.right) (b : p.right _⦋0⦌) :
    IsQCatEquivalence ((S.preSquare f).pointedFiberMap b) ↔
      IsQCatEquivalence (S.pointedFiberMap (f.right.app _ b)) := by
  rw [S.preSquare_pointedFiberMap f hf b]
  exact ⟨fun h ↦ (qCatEquivalenceOfIso (transportCartesianSquareFiberIso f hf b)).isQCatEquivalence
      |>.cancel_left h,
    fun h ↦ (qCatEquivalenceOfIso (transportCartesianSquareFiberIso f hf b)).isQCatEquivalence
      |>.comp h⟩

/-- 概要：pullback 正方形で表現を前合成すると表現となる。
方針：全頂点で fiber 比較の同値性を移す。
規約：底の射の単射性は不要。
使われ方：表現空間の底上の反変関手の射の構成。 -/
lemma LeftTransportSquare.isRepresentation_preSquare {p q : Arrow SSet.{u + 1}}
    [LeftFibration p.hom] [LeftFibration q.hom] (S : LeftTransportSquare q.hom)
    (hS : S.IsRepresentation) (f : p ⟶ q) (hf : IsPullback f.left p.hom q.hom f.right) :
    (S.preSquare f).IsRepresentation := fun b ↦
  (S.preSquare_pointedFiberMap_isQCatEquivalence_iff f hf b).mpr (hS (f.right.app _ b))

end SerrePositivity.InfinityCategories
