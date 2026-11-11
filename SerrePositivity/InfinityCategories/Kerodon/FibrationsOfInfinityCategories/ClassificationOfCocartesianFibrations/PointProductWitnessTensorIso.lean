module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.WitnessBaseIso
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.WitnessTensorIso

/-!
概要：点上の表現のパラメーター族は積の第二射影上の表現空間と同型。
方針：Δ⁰ とパラメーターの積の底を第二射影で正規化する。
規約：全空間と分類図式の全高次データを保持する。
使われ方：区間上の実際の表現空間と点上の表現空間の区間族の比較。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- 概要：Δ⁰ と任意のパラメーターの積は第二射影でパラメーターと同型。
方針：逆で Δ⁰ の唯一の射を第一成分に入れる。
規約：同型の順方向は厳密に第二射影。
使われ方：区間の実際の底を正規化する。 -/
def transportPointTensorIso (K : SSet.{u}) : (Δ[0] : SSet.{u}) ⊗ K ≅ K where
  hom := snd _ _
  inv := lift (stdSimplex.isTerminalObj₀.from K) (𝟙 K)
  hom_inv_id := by
    apply CartesianMonoidalCategory.hom_ext
    · exact stdSimplex.isTerminalObj₀.hom_ext _ _
    · rw [Category.assoc, lift_snd, Category.comp_id, Category.id_comp]
  inv_hom_id := lift_snd _ _

/-- 概要：点との積の正規化はパラメーターの射に自然。
方針：第二射影と左 whiskering の計算。
規約：任意の射 i に対する厳密な等式。
使われ方：区間境界制限と底の同型を同時に保つ。 -/
lemma transportPointTensorIso_naturality {K L : SSet.{u}} (i : L ⟶ K) :
    ((Δ[0] : SSet.{u}) ◁ i) ≫ (transportPointTensorIso K).hom =
      (transportPointTensorIso L).hom ≫ i := whiskerLeft_snd _ _

/-- 概要：単体集合から標準点への標準射影。
方針：Δ⁰ の終対象性による唯一の射を取る。
規約：point 上の表現空間の射影を固定する。
使われ方：点上の表現空間の可縮性。 -/
def transportPointProjection (E : SSet.{u}) : E ⟶ (Δ[0] : SSet.{u}) :=
  stdSimplex.isTerminalObj₀.from E

/-- 概要：Kan 複体の標準点への射影は left fibration。
方針：各次数で高々一点の底への Kan 複体の射の判定を使う。
規約：モデル構造を仮定しない。
使われ方：点上の表現空間の定義。 -/
instance transportPointProjection_leftFibration (E : SSet.{u}) [KanComplex E] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration (transportPointProjection E) where
  mem := by
    intro A D i hi
    cases hi with
    | @intro n k hk =>
      constructor
      intro a b sq
      obtain ⟨H, hH⟩ := KanComplex.hornFilling a
      exact CommSq.HasLift.mk'
        { l := H, fac_left := hH.symm, fac_right := stdSimplex.isTerminalObj₀.hom_ext _ _ }

/-- 概要：Kan 複体とパラメーターの積の第二射影は left fibration。
方針：点射影の積を底の同型で後合成する。
規約：パラメーターの Kan 性は不要。
使われ方：実際の区間上の表現空間の定義。 -/
instance transportProductProjection_leftFibration (E : SSet.{u}) [KanComplex E]
    (K : SSet.{u}) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration (snd E K) := by
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration ((transportPointProjection E ▷ K) ≫ (transportPointTensorIso K).hom)
  infer_instance

/-- 概要：点との積の底を正規化した四角形空間は点上の四角形の族と同型。
方針：底の同型の比較と積の内部 currying の同型を続ける。
規約：全空間は E とパラメーターの積のまま保持する。
使われ方：実際の区間上の四角形の全高次データの比較。 -/
def pointProductSquareTensorIso (E : SSet.{u + 1}) (K : SSet.{u + 1}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquareSpace (snd E K) ≅
      (ihom K).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquareSpace (transportPointProjection E)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSquareBaseIso (transportPointProjection E ▷ K) (snd E K)
    (transportPointTensorIso K) rfl ≪≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSquareTensorIso (transportPointProjection E) K

/-- 概要：積の第二射影上の表現空間は点上の表現空間への内部 Hom と同型。
方針：底の正規化と表現空間の積の同型を続ける。
規約：非空性と小ささは仮定しない。
使われ方：Kerodon Lemma 5.6.9.2（Tag 02SR） の点上の表現の区間族。 -/
def pointProductWitnessTensorIso (E : SSet.{u + 1}) [KanComplex E] (K : SSet.{u + 1}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportWitnessSpace (snd E K) ≅
      (ihom K).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportWitnessSpace (transportPointProjection E)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportWitnessBaseIso (transportPointProjection E ▷ K) (transportPointTensorIso K) ≪≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportWitnessTensorIso (transportPointProjection E) K

/-- 概要：点上の表現の族との比較は周囲の四角形の同型を回収する。
方針：底の同型と積の同型の二つの包含公式を続ける。
規約：全高次単体の射の厳密な一致。
使われ方：実際の区間の境界制限との自然性。 -/
lemma pointProductWitnessTensorIso_hom_ι (E : SSet.{u + 1}) [KanComplex E]
    (K : SSet.{u + 1}) :
    (pointProductWitnessTensorIso E K).hom ≫ (ihom K).map
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportWitnessSpaceι (transportPointProjection E)) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportWitnessSpaceι (snd E K) ≫ (pointProductSquareTensorIso E K).hom := by
  dsimp only [pointProductWitnessTensorIso, pointProductSquareTensorIso, Iso.trans_hom]
  rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportWitnessTensorIso_hom_ι, ← Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportWitnessBaseIso_hom_ι, Category.assoc]
  rfl

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
