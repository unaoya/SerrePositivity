module

public import SerrePositivity.InfinityCategories.F1.TransportSquareTensorPreLaws

/-!
概要：積上の実際の表現のパラメーター制限と内部 Hom の前合成の自然性。
方針：四角形の制限が各パラメーターの表現条件を保つことを使う。
規約：底側と全空間側の両方の射を厳密に保つ。
使われ方：区間境界制限定理を点上の表現空間の対角へ移す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：積上の四角形のパラメーター制限は表現条件を保つ。
方針：各頂点での評価を像の頂点での元の評価へ移す。
規約：パラメーターの射の単射性と充填性は不要。
使われ方：四角形空間の制限を実際の表現空間へ持ち上げる。 -/
lemma LeftTransportSquare.isRepresentation_tensorPre {E B K L : SSet.{u + 1}}
    {p : E ⟶ B} [LeftFibration p] (S : LeftTransportSquare (p ▷ K))
    (hS : S.IsRepresentation) (i : L ⟶ K) : (S.tensorPre i).IsRepresentation := by
  apply (S.tensorPre i).isRepresentation_tensor_iff.mpr
  intro l
  rw [S.tensorPre_tensorAt]
  exact S.isRepresentation_tensor_iff.mp hS (i.app _ l)

/-- 概要：積上の実際の表現空間のパラメーター制限。
方針：周囲の四角形の制限を表現条件の全部分複体へ持ち上げる。
規約：全高次単体の射として構成する。
使われ方：境界族への制限と内部 Hom の前合成を比較する。 -/
def transportWitnessTensorPre {E B : SSet.{u + 1}} (p : E ⟶ B) [LeftFibration p]
    {K L : SSet.{u + 1}} (i : L ⟶ K) :
    transportWitnessSpace (p ▷ K) ⟶ transportWitnessSpace (p ▷ L) :=
  fullSubcomplexLift (IsTransportWitnessVertex (p ▷ L))
    (transportWitnessSpaceι (p ▷ K) ≫ transportSquareTensorPre p i) (by
      intro v
      obtain ⟨R, rfl⟩ := transportWitnessVertex_surjective (p ▷ K) v
      change IsTransportWitnessVertex (p ▷ L)
        ((transportSquareTensorPre p i).app _ (transportSquareVertex R.toSquare))
      rw [transportSquareTensorPre_vertex, isTransportWitnessVertex_iff_isRepresentation]
      exact R.toSquare.isRepresentation_tensorPre R.toSquare_isRepresentation i)

/-- 概要：積の表現空間の制限は周囲の四角形の制限を厳密に回収する。
方針：全部分複体への lift の包含公式。
規約：全高次単体での射の等式。
使われ方：実際の境界制限との自然性の比較。 -/
lemma transportWitnessTensorPre_ι {E B : SSet.{u + 1}} (p : E ⟶ B) [LeftFibration p]
    {K L : SSet.{u + 1}} (i : L ⟶ K) :
    transportWitnessTensorPre p i ≫ transportWitnessSpaceι (p ▷ L) =
      transportWitnessSpaceι (p ▷ K) ≫ transportSquareTensorPre p i := fullSubcomplexLift_ι _ _ _

/-- 概要：積上の表現空間と内部 Hom の同型は任意のパラメーター制限に自然。
方針：包含後に四角形の currying の自然性を適用する。
規約：境界上の分類図式と全空間の射の両方を厳密に保つ。
使われ方：点上の表現空間の区間族とその境界族の比較。 -/
lemma transportWitnessTensorIso_hom_naturality {E B : SSet.{u + 1}}
    (p : E ⟶ B) [LeftFibration p] {K L : SSet.{u + 1}} (i : L ⟶ K) :
    transportWitnessTensorPre p i ≫ (transportWitnessTensorIso p L).hom =
      (transportWitnessTensorIso p K).hom ≫ (pre i).app (transportWitnessSpace p) := by
  let : Mono (transportWitnessSpaceι p) := inferInstanceAs
    (Mono (fullSubcomplexOnVertices (transportSquareSpace p) (IsTransportWitnessVertex p)).ι)
  have : Mono ((ihom L).map (transportWitnessSpaceι p)) := (ihom L).map_mono _
  apply (cancel_mono ((ihom L).map (transportWitnessSpaceι p))).1
  rw [Category.assoc, transportWitnessTensorIso_hom_ι, ← Category.assoc,
    transportWitnessTensorPre_ι]
  simp only [Category.assoc]
  rw [transportSquareTensorIso_hom_naturality, pre_comm_ihom_map]
  simp only [← Category.assoc]
  rw [transportWitnessTensorIso_hom_ι]

end SerrePositivity.InfinityCategories
