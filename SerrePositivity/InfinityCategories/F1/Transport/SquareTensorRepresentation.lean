module

public import SerrePositivity.InfinityCategories.F1.Transport.SquareTensorAt

/-!
概要：積上の四角形が表現となることは各パラメーターで表現となることと同値。
方針：固定パラメーターの fiber 同型で比較射の同値性を移す。
規約：パラメーターの Kan 性は不要。
使われ方：表現空間と内部 Hom の厳密な比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

attribute [local instance] vertexFiber_kanComplex_of_leftFibration

/-- 概要：固定パラメーターの四角形の fiber 同値条件は元の対の頂点の条件と同値。
方針：積の fiber 同型の逆との合成を包含後に確認し二対三則を使う。
規約：底とパラメーターの頂点は任意。
使われ方：積上の表現条件の各パラメーターでの判定。 -/
lemma LeftTransportSquare.tensorAt_pointedFiberMap_isQCatEquivalence_iff
    {E B K : SSet.{u + 1}} {p : E ⟶ B} [LeftFibration p]
    (S : LeftTransportSquare (p ▷ K)) (k : K _⦋0⦌) (b : B _⦋0⦌) :
    IsQCatEquivalence ((S.tensorAt k).pointedFiberMap b) ↔
      IsQCatEquivalence (S.pointedFiberMap (b, k)) := by
  let k' := (SSet.const k : B ⟶ K).app (Opposite.op ⦋0⦌) b
  have hk : k' = k := by
    simp only [k', SSet.const_app, SimplexCategory.const_eq_id, op_id, Functor.map_id_apply]
    rfl
  let e := (transportTensorFiberIso p K b k').symm
  have h : (S.tensorAt k).pointedFiberMap b = e.hom ≫ S.pointedFiberMap (b, k') := by
    apply vertexFiber_hom_ext pointedSpaceProjection ((S.tensorAt k).diagram.app _ b)
    rw [(S.tensorAt k).pointedFiberMap_ι, Category.assoc]
    change vertexFiberι p b ≫ (lift (𝟙 E) (SSet.const k) ≫ S.pointedMap) =
      e.hom ≫ S.pointedFiberMap (b, k') ≫
        vertexFiberι pointedSpaceProjection (S.diagram.app _ (b, k'))
    rw [S.pointedFiberMap_ι, ← Category.assoc]
    change _ = ((transportTensorFiberIso p K b k').inv ≫
      vertexFiberι (p ▷ K) (b, k')) ≫ S.pointedMap
    rw [transportTensorFiberIso_inv_ι, hk, Category.assoc]
  have he := (qCatEquivalenceOfIso e).isQCatEquivalence
  rw [h]
  constructor
  · intro hcomp
    have hf : IsQCatEquivalence (S.pointedFiberMap (b, k')) := he.cancel_left hcomp
    rw [hk] at hf
    exact hf
  · intro hf
    have hf' : IsQCatEquivalence (S.pointedFiberMap (b, k')) := by
      rw [hk]
      exact hf
    exact he.comp hf'

/-- 概要：積上の四角形の表現条件は各パラメーターでの表現条件と同値。
方針：積の頂点の二成分ごとに fiber 同値条件を比較する。
規約：全ての頂点を扱い、高次の条件を存在仮定に置かない。
使われ方：全部分複体への currying 同型の制限。 -/
lemma LeftTransportSquare.isRepresentation_tensor_iff {E B K : SSet.{u + 1}}
    {p : E ⟶ B} [LeftFibration p] (S : LeftTransportSquare (p ▷ K)) :
    S.IsRepresentation ↔ ∀ k : K _⦋0⦌, (S.tensorAt k).IsRepresentation := by
  constructor
  · intro h k b
    exact (S.tensorAt_pointedFiberMap_isQCatEquivalence_iff k b).mpr (h (b, k))
  · intro h bk
    exact (S.tensorAt_pointedFiberMap_isQCatEquivalence_iff bk.2 bk.1).mp (h bk.2 bk.1)

end SerrePositivity.InfinityCategories
