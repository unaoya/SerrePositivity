module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.RelativeJoinBaseProjection
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.RelativeJoinEndpointPullbacks

/-!
概要：同じ底上の射を区間と底の積の上の relative join に実現する。
方針：relative join の区間付き終域への射影に元の底への射を続ける。
規約：left fibration 性は後続で証明し定義に仮定しない。
使われ方：非可逆な相対射を coherent な変換へ復元する全空間。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- 概要：相対射の relative join から区間と元の底の積への射影。
方針：区間付き終域の射影に底への射を続ける。
規約：零端は f の始域、一端は終域。
使われ方：射の coherent な分類の実現の候補。 -/
def relativeArrowCollageProjection {E F B : SSet.{u}} (f : E ⟶ F) (q : F ⟶ B) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoin f (𝟙 F) ⟶ (Δ[1] : SSet.{u}) ⊗ B :=
  pullback.snd (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap f (𝟙 F)) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.joinDiagonal F) ≫ (Δ[1] ◁ q)

/-- 概要：元の底を忘れると relative join の区間射影に一致する。
方針：テンソルの第一射影の自然性を使う。
規約：区間は第一因子。
使われ方：時間の切断によるホーンの分岐。 -/
lemma relativeArrowCollageProjection_fst {E F B : SSet.{u}} (f : E ⟶ F) (q : F ⟶ B) :
    relativeArrowCollageProjection f q ≫ fst Δ[1] B = _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinProjection f (𝟙 F) := by
  rw [relativeArrowCollageProjection, Category.assoc, whiskerLeft_fst]
  rfl

/-- 概要：時間を忘れると relative join の終域側の係数射影に元の底への射を続ける。
方針：テンソルの第二射影の自然性を使う。
規約：係数は元の終域 F。
使われ方：元の底のホーンを終域側で充填する条件。 -/
lemma relativeArrowCollageProjection_snd {E F B : SSet.{u}} (f : E ⟶ F) (q : F ⟶ B) :
    relativeArrowCollageProjection f q ≫ snd Δ[1] B = _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinBaseProjection f (𝟙 F) ≫ q := by
  rw [relativeArrowCollageProjection, Category.assoc, whiskerLeft_snd]
  rfl

/-- 概要：relative join の零端の射影は元の始域の射影と区間の零端の合成。
方針：relative join の第一因子の包含と prism の自然性を使う。
規約：底上の射の可換性を厳密に用いる。
使われ方：実現の始域の固定。 -/
lemma relativeArrowCollageProjection_inl {E F B : SSet.{u}}
    (p : E ⟶ B) (q : F ⟶ B) (f : E ⟶ F) (hf : f ≫ q = p) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinInl f (𝟙 F) ≫ relativeArrowCollageProjection f q = p ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 B := by
  rw [relativeArrowCollageProjection, ← Category.assoc]
  rw [show _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinInl f (𝟙 F) ≫ pullback.snd _ _ = f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 F from
    pullback.lift_snd _ _ _]
  rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint_naturality, ← Category.assoc, hf]

/-- 概要：relative join の一端の射影は元の終域の射影と区間の一端の合成。
方針：第二因子の包含と prism の自然性を使う。
規約：底への構造射は q。
使われ方：実現の終域の固定。 -/
lemma relativeArrowCollageProjection_inr {E F B : SSet.{u}} (f : E ⟶ F) (q : F ⟶ B) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinInr f (𝟙 F) ≫ relativeArrowCollageProjection f q = q ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 B := by
  rw [relativeArrowCollageProjection, ← Category.assoc]
  rw [show _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinInr f (𝟙 F) ≫ pullback.snd _ _ = (𝟙 F) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 F from
    pullback.lift_snd _ _ _]
  rw [Category.id_comp, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint_naturality]

/-- 概要：relative join の標準 prism は元の始域の底への射を区間全体で被覆する。
方針：prism の第二射影とテンソルの合成則を計算する。
規約：始域の全ての単体を同時に扱う。
使われ方：復元した変換が元の相対射を回収することの比較。 -/
lemma relativeArrowCollageProjection_prism {E F B : SSet.{u}}
    (p : E ⟶ B) (q : F ⟶ B) (f : E ⟶ F) (hf : f ≫ q = p) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinPrism f ≫ relativeArrowCollageProjection f q = (Δ[1] : SSet.{u}) ◁ p := by
  rw [relativeArrowCollageProjection, ← Category.assoc]
  rw [show _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinPrism f ≫ pullback.snd _ _ = Δ[1] ◁ f from pullback.lift_snd _ _ _]
  rw [← whiskerLeft_comp, hf]

/-- 概要：始域の包含は区間と底の積の零端への pullback。
方針：区間だけの端点の pullback から底を含む正方形を消去する。
規約：射影の充填性はまだ不要。
使われ方：実現の零端を元の left fibration と厳密に同定する。 -/
lemma relativeArrowCollage_inl_isPullback {E F B : SSet.{u}}
    (p : E ⟶ B) (q : F ⟶ B) (f : E ⟶ F) (hf : f ≫ q = p) :
    IsPullback (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinInl f (𝟙 F)) p
      (relativeArrowCollageProjection f q) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 B) := by
  have hs : IsPullback (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinInl f (𝟙 F))
      (p ≫ stdSimplex.isTerminalObj₀.from B)
      (relativeArrowCollageProjection f q ≫ fst Δ[1] B)
      (SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 2))) := by
    rw [relativeArrowCollageProjection_fst]
    convert _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinInl_endpoint_isPullback f (𝟙 F) using 1
    exact stdSimplex.isTerminalObj₀.hom_ext _ _
  exact hs.of_bot (relativeArrowCollageProjection_inl p q f hf)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.isPullback_prismEndpoint_fst 0 B)

/-- 概要：終域の包含は区間と底の積の一端への pullback。
方針：区間だけの終端の pullback から底を含む正方形を消去する。
規約：元の終域の射影を厳密に保つ。
使われ方：実現の一端を元の left fibration と同定する。 -/
lemma relativeArrowCollage_inr_isPullback {E F B : SSet.{u}} (f : E ⟶ F) (q : F ⟶ B) :
    IsPullback (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinInr f (𝟙 F)) q
      (relativeArrowCollageProjection f q) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 B) := by
  have hs : IsPullback (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinInr f (𝟙 F))
      (q ≫ stdSimplex.isTerminalObj₀.from B)
      (relativeArrowCollageProjection f q ≫ fst Δ[1] B)
      (SSet.const (stdSimplex.obj₀Equiv.symm (1 : Fin 2))) := by
    rw [relativeArrowCollageProjection_fst]
    convert _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinInr_endpoint_isPullback f (𝟙 F) using 1
    exact stdSimplex.isTerminalObj₀.hom_ext _ _
  exact hs.of_bot (relativeArrowCollageProjection_inr f q) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.isPullback_prismEndpoint_fst 1 B)

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
