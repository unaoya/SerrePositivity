module

public import SerrePositivity.InfinityCategories.F1.Transport.WitnessTensorPre
public import SerrePositivity.InfinityCategories.F1.Transport.TensorPullbackIso

/-!
概要：積のパラメーター制限を実際の表現空間の底変換制限と同定する。
方針：引き戻し全空間の同型を介し、両射影の前合成を計算する。
規約：分類図式と全空間の写像をともに厳密に保つ。
使われ方：区間の実際の境界制限と内部 Hom の境界制限を結ぶ。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

local instance {E B D : SSet.{u}} (p : E ⟶ B) [LeftFibration p] (g : D ⟶ B) :
    LeftFibration (pullback.snd p g) :=
  ⟨leftFibrations.pullback_snd p g (LeftFibration.mem (p := p))⟩

/-- 概要：積の四角形の制限は実際の底変換制限に全空間の同型を続けた射。
方針：両射影で引き戻し同型と内部 Hom の前合成の合成則を使う。
規約：全高次単体で厳密に一致する。
使われ方：表現空間の底変換制限の比較の周囲の等式。 -/
lemma transportSquareTensorPre_eq_restriction {E B K L : SSet.{u + 1}}
    (p : E ⟶ B) (i : L ⟶ K) :
    transportSquareRestriction (p ▷ K) (B ◁ i) ≫
        transportSquareTotalPre (p ▷ L) (pullback.snd (p ▷ K) (B ◁ i))
          (transportTensorPullbackIso p i).hom (transportTensorPullbackIso_hom_snd p i) =
      transportSquareTensorPre p i := by
  apply pullback.hom_ext
  · change (_ ≫ _) ≫ transportSquarePointed (p ▷ L) =
      transportSquareTensorPre p i ≫ transportSquarePointed (p ▷ L)
    rw [Category.assoc, transportSquareTotalPre_pointed, ← Category.assoc,
      transportSquareRestriction_pointed, transportSquareTensorPre_pointed, Category.assoc,
      ← NatTrans.comp_app, ← pre_map, transportTensorPullbackIso_hom_fst]
  · change (_ ≫ _) ≫ transportSquareDiagram (p ▷ L) =
      transportSquareTensorPre p i ≫ transportSquareDiagram (p ▷ L)
    rw [Category.assoc, transportSquareTotalPre_diagram, transportSquareRestriction_diagram,
      transportSquareTensorPre_diagram]

/-- 概要：積の実際の表現空間の制限は底変換制限と全空間同型の合成。
方針：全部分複体の包含後に四角形の同じ比較を適用する。
規約：指定した境界の両側の射を厳密に保持する。
使われ方：実際の区間境界制限定理をパラメーター制限へ移す。 -/
lemma transportWitnessTensorPre_eq_restriction {E B K L : SSet.{u + 1}}
    (p : E ⟶ B) [LeftFibration p] (i : L ⟶ K) :
    transportWitnessRestriction (p ▷ K) (B ◁ i) ≫
        (transportWitnessTotalIso (p ▷ L) (pullback.snd (p ▷ K) (B ◁ i))
          (transportTensorPullbackIso p i) (transportTensorPullbackIso_hom_snd p i)).hom =
      transportWitnessTensorPre p i := by
  let : Mono (transportWitnessSpaceι (p ▷ L)) := inferInstanceAs
    (Mono (fullSubcomplexOnVertices (transportSquareSpace (p ▷ L))
      (IsTransportWitnessVertex (p ▷ L))).ι)
  apply (cancel_mono (transportWitnessSpaceι (p ▷ L))).1
  rw [Category.assoc, transportWitnessTotalIso_hom_ι, ← Category.assoc,
    transportWitnessRestriction_ι, transportWitnessTensorPre_ι]
  simp only [Category.assoc]
  rw [transportSquareTensorPre_eq_restriction]

/-- 概要：積の表現空間の内部 Hom 表示は実際の底変換制限と可換。
方針：全空間同型による翻訳とパラメーター制限の自然性を続ける。
規約：全高次単体を保つ実際の表現空間の射についての等式。
使われ方：区間上の表現空間の境界制限を点上の族の境界制限へ移す。 -/
lemma transportWitnessTensorIso_restriction_naturality {E B K L : SSet.{u + 1}}
    (p : E ⟶ B) [LeftFibration p] (i : L ⟶ K) :
    (transportWitnessRestriction (p ▷ K) (B ◁ i) ≫
        (transportWitnessTotalIso (p ▷ L) (pullback.snd (p ▷ K) (B ◁ i))
          (transportTensorPullbackIso p i) (transportTensorPullbackIso_hom_snd p i)).hom) ≫
        (transportWitnessTensorIso p L).hom =
      (transportWitnessTensorIso p K).hom ≫ (pre i).app (transportWitnessSpace p) := by
  rw [transportWitnessTensorPre_eq_restriction, transportWitnessTensorIso_hom_naturality]

end SerrePositivity.InfinityCategories
