module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.JoinShiftCoefficient
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RelativeJoinLocalCone

/-!
概要：join の移動 prism を relative join へ持ち上げる。
方針：全単体で証明した係数の等式と左端の両立を pullback の条件にする。
規約：時間は第一因子、δ の単射性や quasicategory 性は不要。
使われ方：局所比較余錐と指定変換の輸送の接続。

対応節は Kerodon 7.3（Tag 02Y1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions

/-- 概要：移動 prism の join の切断を区間として読む。
方針：標準の区間射影を後合成する。
規約：元の時間と元の join の時間をまとめた時間。
使われ方：relative join の係数の区間成分。 -/
def kanJoinShiftTime (A B : SSet.{u}) :
    (Δ[1] : SSet.{u}) ⊗ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join A B ⟶ (Δ[1] : SSet.{u}) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinShiftPrism A B ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.joinIntervalProjection A (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join A B)

/-- 概要：移動の始点の時間は元の join の区間射影。
方針：prism の始端と区間射影の自然性。
規約：全単体での等式。
使われ方：補正の始点の回収。 -/
lemma kanJoinShiftTime_zero (A B : SSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join A B) ≫ kanJoinShiftTime A B = _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.joinIntervalProjection A B := by
  rw [kanJoinShiftTime, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinShiftPrism_zero,
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.joinIntervalProjection_naturality]

/-- 概要：移動の終点の時間は一に定値。
方針：prism の終端は右包含である。
規約：係数自体は忘れない。
使われ方：補正の右端の図式の回収。 -/
lemma kanJoinShiftTime_one (A B : SSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join A B) ≫ kanJoinShiftTime A B =
      SSet.const (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) := by
  rw [kanJoinShiftTime, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinShiftPrism_one, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.joinIntervalProjection_inr]

/-- 概要：左因子上の時間は prism の時間そのもの。
方針：対角の区間成分の計算を使う。
規約：左境界の指定変換の時間を保持する。
使われ方：輸送の図式部分の同定。 -/
lemma kanJoinShiftTime_left (A B : SSet.{u}) :
    ((Δ[1] : SSet.{u}) ◁ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl A B) ≫ kanJoinShiftTime A B = fst Δ[1] A := by
  rw [kanJoinShiftTime, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinShiftPrism_left, Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.joinIntervalProjection_naturality, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.joinDiagonal_joinIntervalProjection]

/-- 概要：右因子上の時間は全時刻で一。
方針：prism の右境界と右包含の区間の計算を使う。
規約：右因子は全時刻で固定する。
使われ方：固定頂点条件。 -/
lemma kanJoinShiftTime_right (A B : SSet.{u}) :
    ((Δ[1] : SSet.{u}) ◁ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr A B) ≫ kanJoinShiftTime A B =
      SSet.const (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) := by
  rw [kanJoinShiftTime, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinShiftPrism_right, Category.assoc,
    Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.joinIntervalProjection_inr, SSet.comp_const, SSet.comp_const]

/-- 概要：元の局所図式から右端の図式へ移す relative join 上の prism。
方針：移動 prism の左右を a と H で写し、元の H を係数として pullback に入れる。
規約：左端で H が a≫δ に一致することだけを仮定する。
使われ方：局所比較余錐の実際の輸送。 -/
def kanRelativeJoinShiftPrism {A B K C : SSet.{u}} (δ : K ⟶ C) (a : A ⟶ K)
    (H : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join A B ⟶ C) (hA : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl A B ≫ H = a ≫ δ) :
    (Δ[1] : SSet.{u}) ⊗ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join A B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoin δ (𝟙 C) :=
  pullback.lift (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinShiftPrism A B ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap a H)
    (lift (kanJoinShiftTime A B) (snd (Δ[1] : SSet.{u}) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join A B) ≫ H)) (by
      have h : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap a H ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap δ (𝟙 C) =
          _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl A B) (𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join A B)) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap H H := by
        rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap_comp, Category.comp_id, ← hA, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap_comp, Category.id_comp]
      rw [Category.assoc, h, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinShiftPrism_coefficient,
        Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.joinDiagonal_naturality, ← Category.assoc]
      rfl)

/-- 概要：移動 prism の通常の join への成分。
方針：pullback の第一射影の計算則。
規約：構成した raw な射の等式。
使われ方：四境界の第一成分の照合。 -/
lemma kanRelativeJoinShiftPrism_fst {A B K C : SSet.{u}} (δ : K ⟶ C) (a : A ⟶ K)
    (H : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join A B ⟶ C) (hA : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl A B ≫ H = a ≫ δ) :
    kanRelativeJoinShiftPrism δ a H hA ≫ pullback.fst (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap δ (𝟙 C)) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.joinDiagonal C) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinShiftPrism A B ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap a H := pullback.lift_fst _ _ _

/-- 概要：移動 prism の区間付き係数。
方針：pullback の第二射影の計算則。
規約：係数 H は元の時間によらない図式。
使われ方：四境界の第二成分の照合。 -/
lemma kanRelativeJoinShiftPrism_snd {A B K C : SSet.{u}} (δ : K ⟶ C) (a : A ⟶ K)
    (H : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join A B ⟶ C) (hA : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl A B ≫ H = a ≫ δ) :
    kanRelativeJoinShiftPrism δ a H hA ≫ pullback.snd (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap δ (𝟙 C)) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.joinDiagonal C) =
      lift (kanJoinShiftTime A B) (snd (Δ[1] : SSet.{u}) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join A B) ≫ H) :=
  pullback.lift_snd _ _ _

/-- 概要：持ち上げた prism の始点は元の局所図式の標準持ち上げ。
方針：二つの射影で始端と元の時間の式を使う。
規約：自然同型でなく射の等式。
使われ方：局所余錐と輸送の始端の同定。 -/
lemma kanRelativeJoinShiftPrism_zero {A B K C : SSet.{u}} (δ : K ⟶ C) (a : A ⟶ K)
    (H : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join A B ⟶ C) (hA : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl A B ≫ H = a ≫ δ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join A B) ≫ kanRelativeJoinShiftPrism δ a H hA =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeJoinLift δ (𝟙 C) a (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr A B ≫ H) H hA (by rw [Category.comp_id]) := by
  apply pullback.hom_ext
  · rw [Category.assoc, kanRelativeJoinShiftPrism_fst, ← Category.assoc,
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinShiftPrism_zero, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap_comp, Category.id_comp, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeJoinLift_fst]
  · rw [Category.assoc, kanRelativeJoinShiftPrism_snd, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeJoinLift_snd]
    apply CartesianMonoidalCategory.hom_ext
    · rw [Category.assoc, lift_fst, lift_fst, kanJoinShiftTime_zero]
    · simp only [Category.assoc, lift_snd]
      rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.prismEndpoint_snd, Category.id_comp]

/-- 概要：持ち上げた prism の終点は係数図式を右端に入れたもの。
方針：右包含と一に定値な時間を二つの射影で計算する。
規約：H を全単体で保持する。
使われ方：輸送の標準比較余錐の回収。 -/
lemma kanRelativeJoinShiftPrism_one {A B K C : SSet.{u}} (δ : K ⟶ C) (a : A ⟶ K)
    (H : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join A B ⟶ C) (hA : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl A B ≫ H = a ≫ δ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join A B) ≫ kanRelativeJoinShiftPrism δ a H hA =
      H ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinInr δ (𝟙 C) := by
  apply pullback.hom_ext
  · rw [Category.assoc, kanRelativeJoinShiftPrism_fst, ← Category.assoc,
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinShiftPrism_one, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr_joinMap, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinInr_fst]
  · rw [Category.assoc, kanRelativeJoinShiftPrism_snd]
    simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinInr, Category.assoc, pullback.lift_snd, Category.id_comp]
    apply CartesianMonoidalCategory.hom_ext
    · simp only [Category.assoc, lift_fst, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint, SSet.comp_const]
      exact kanJoinShiftTime_one A B
    · simp only [Category.assoc, lift_snd, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint]
      rfl

/-- 概要：持ち上げた prism の左境界は指定した a に沿う標準 prism。
方針：対角の自然性と H の左端の等式を両射影で使う。
規約：左端の自然変換を全時間で保持する。
使われ方：輸送の diagram フィールド。 -/
lemma kanRelativeJoinShiftPrism_left {A B K C : SSet.{u}} (δ : K ⟶ C) (a : A ⟶ K)
    (H : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join A B ⟶ C) (hA : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl A B ≫ H = a ≫ δ) :
    ((Δ[1] : SSet.{u}) ◁ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl A B) ≫ kanRelativeJoinShiftPrism δ a H hA =
      ((Δ[1] : SSet.{u}) ◁ a) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinPrism δ := by
  apply pullback.hom_ext
  · rw [Category.assoc, kanRelativeJoinShiftPrism_fst, ← Category.assoc,
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinShiftPrism_left]
    simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinPrism, Category.assoc, pullback.lift_fst]
    rw [← Category.assoc ((Δ[1] : SSet.{u}) ◁ a), _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.joinDiagonal_naturality]
    simp only [Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap_comp, Category.id_comp, Category.comp_id, hA]
  · rw [Category.assoc, kanRelativeJoinShiftPrism_snd]
    simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinPrism, Category.assoc, pullback.lift_snd]
    apply CartesianMonoidalCategory.hom_ext
    · simp only [Category.assoc, lift_fst, whiskerLeft_fst]
      exact kanJoinShiftTime_left A B
    · simp only [Category.assoc, lift_snd, whiskerLeft_snd_assoc]
      rw [hA]
      rfl

/-- 概要：持ち上げた prism の右境界は時間に定値な右端の図式。
方針：右境界の固定と一の時間を二つの射影で照合する。
規約：B=Δ⁰ の場合に頂点固定の条件になる。
使われ方：輸送の fixedVertex フィールド。 -/
lemma kanRelativeJoinShiftPrism_right {A B K C : SSet.{u}} (δ : K ⟶ C) (a : A ⟶ K)
    (H : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join A B ⟶ C) (hA : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl A B ≫ H = a ≫ δ) :
    ((Δ[1] : SSet.{u}) ◁ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr A B) ≫ kanRelativeJoinShiftPrism δ a H hA =
      snd (Δ[1] : SSet.{u}) B ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr A B ≫ H ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinInr δ (𝟙 C) := by
  apply pullback.hom_ext
  · rw [Category.assoc, kanRelativeJoinShiftPrism_fst, ← Category.assoc,
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinShiftPrism_right]
    simp only [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr_joinMap, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinInr_fst]
  · rw [Category.assoc, kanRelativeJoinShiftPrism_snd]
    simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinInr, Category.assoc, pullback.lift_snd, Category.id_comp]
    apply CartesianMonoidalCategory.hom_ext
    · simp only [Category.assoc, lift_fst, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint, SSet.comp_const]
      exact kanJoinShiftTime_right A B
    · simp only [Category.assoc, lift_snd, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint, Category.comp_id,
        whiskerLeft_snd_assoc]

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions
