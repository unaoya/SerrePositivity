module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.JoinRightShiftCoefficient
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RelativeJoinLocalCone

/-!
概要：右移動 prism の relative join への持ち上げ。
方針：係数の可換性を pullback 条件とし、四境界を両射影で比較する。
規約：時間は第二因子、δ の単射性や quasicategory 性は不要。
使われ方：右 Kan 拡張の局所比較錐と指定変換の輸送の接続。

対応節は Kerodon 7.3（Tag 02Y1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions

/-- 概要：右移動後の join の切断を区間として読む。
方針：右移動 prism に区間射影を後合成する。
規約：元の時間と元の join の時間をまとめる。
使われ方：右 relative join の係数の区間成分。 -/
def kanJoinRightShiftTime (A B : SSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join A B ⊗ (Δ[1] : SSet.{u}) ⟶ (Δ[1] : SSet.{u}) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinRightShiftPrism A B ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.joinIntervalProjection (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join A B) B

/-- 概要：右移動の始点の時間は零に定値。
方針：始点が左包含であることを使う。
規約：全単体での射の等式。
使われ方：右輸送の start 条件。 -/
lemma kanJoinRightShiftTime_zero (A B : SSet.{u}) :
    SSet.ι₀ ≫ kanJoinRightShiftTime A B =
      SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) := by
  rw [kanJoinRightShiftTime, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinRightShiftPrism_zero,
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.joinIntervalProjection_inl]

/-- 概要：右移動の終点の時間は元の join の時間。
方針：終点の joinMap と区間射影の自然性。
規約：元の切断を保持する。
使われ方：局所比較錐の回収。 -/
lemma kanJoinRightShiftTime_one (A B : SSet.{u}) :
    SSet.ι₁ ≫ kanJoinRightShiftTime A B = _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.joinIntervalProjection A B := by
  rw [kanJoinRightShiftTime, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinRightShiftPrism_one,
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.joinIntervalProjection_naturality]

/-- 概要：右移動の左境界の時間は零に定値。
方針：左因子の固定と左包含の時間を計算する。
規約：全時刻で同じ左端にある。
使われ方：右輸送の fixedVertex 条件。 -/
lemma kanJoinRightShiftTime_left (A B : SSet.{u}) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl A B ▷ (Δ[1] : SSet.{u})) ≫ kanJoinRightShiftTime A B =
      SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) := by
  rw [kanJoinRightShiftTime, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinRightShiftPrism_left,
    Category.assoc, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.joinIntervalProjection_inl,
    SSet.comp_const, SSet.comp_const]

/-- 概要：右移動の右境界の時間は元の prism の時間。
方針：区間付き対角の時間と braiding の射影を計算する。
規約：第二因子が時間。
使われ方：右輸送の diagram 条件。 -/
lemma kanJoinRightShiftTime_right (A B : SSet.{u}) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr A B ▷ (Δ[1] : SSet.{u})) ≫ kanJoinRightShiftTime A B = snd B Δ[1] := by
  rw [kanJoinRightShiftTime, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinRightShiftPrism_right,
    Category.assoc, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.joinIntervalProjection_naturality,
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.joinDiagonal_joinIntervalProjection]
  rfl

/-- 概要：右 relative join の標準指定変換の prism。
方針：右因子の対角を δ と恒等射で写し、底の区間付き δ と合わせる。
規約：始点は δ に沿う左包含、終点は右包含。
使われ方：右 Kan 拡張の指定自然変換。 -/
def kanRelativeJoinRightPrism {K C : SSet.{u}} (δ : K ⟶ C) :
    K ⊗ (Δ[1] : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoin (𝟙 C) δ :=
  pullback.lift
    ((β_ K (Δ[1] : SSet.{u})).hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.joinDiagonal K ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap δ (𝟙 K))
    ((β_ K (Δ[1] : SSet.{u})).hom ≫ ((Δ[1] : SSet.{u}) ◁ δ)) (by
      simp only [Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap_comp, Category.comp_id,
        Category.id_comp, ← _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.joinDiagonal_naturality])

/-- 概要：標準右 prism の始点は δ に沿う左端。
方針：対角の始点を両射影で比較する。
規約：時刻零。
使われ方：右指定変換の始点。 -/
lemma kanRelativeJoinRightPrism_zero {K C : SSet.{u}} (δ : K ⟶ C) :
    SSet.ι₀ ≫ kanRelativeJoinRightPrism δ = δ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinInl (𝟙 C) δ := by
  apply pullback.hom_ext
  · simp only [kanRelativeJoinRightPrism, Category.assoc, pullback.lift_fst,
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinInl_fst]
    change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 K ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.joinDiagonal K ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap δ (𝟙 K) = _
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.prismEndpoint_zero_joinDiagonal, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl_joinMap]
  · simp only [kanRelativeJoinRightPrism, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinInl, Category.assoc,
      pullback.lift_snd, Category.id_comp]
    rfl

/-- 概要：標準右 prism の終点は右端。
方針：対角の終点を両射影で比較する。
規約：時刻一。
使われ方：右指定変換の終点。 -/
lemma kanRelativeJoinRightPrism_one {K C : SSet.{u}} (δ : K ⟶ C) :
    SSet.ι₁ ≫ kanRelativeJoinRightPrism δ = _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinInr (𝟙 C) δ := by
  apply pullback.hom_ext
  · simp only [kanRelativeJoinRightPrism, Category.assoc, pullback.lift_fst,
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinInr_fst]
    change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 K ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.joinDiagonal K ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap δ (𝟙 K) = _
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.prismEndpoint_one_joinDiagonal, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr_joinMap, Category.id_comp]
  · simp only [kanRelativeJoinRightPrism, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinInr, Category.assoc,
      pullback.lift_snd]
    rfl

/-- 概要：左端の係数図式から元の局所図式へ移す右 relative join の prism。
方針：右移動 prism の左右を H と b で写し、元の H を係数に使う。
規約：右端で H が b≫δ に一致することだけを仮定する。
使われ方：右比較錐の実際の輸送。 -/
def kanRelativeJoinRightShiftPrism {A B K C : SSet.{u}} (δ : K ⟶ C) (b : B ⟶ K)
    (H : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join A B ⟶ C) (hB : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr A B ≫ H = b ≫ δ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join A B ⊗ (Δ[1] : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoin (𝟙 C) δ :=
  pullback.lift (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinRightShiftPrism A B ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap H b)
    (lift (kanJoinRightShiftTime A B) (fst (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join A B) (Δ[1] : SSet.{u}) ≫ H)) (by
      have h : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap H b ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 C) δ =
          _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join A B)) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr A B) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap H H := by
        rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap_comp, Category.comp_id, ← hB, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap_comp, Category.id_comp]
      rw [Category.assoc, h, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinRightShiftPrism_coefficient,
        Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.joinDiagonal_naturality, ← Category.assoc]
      rfl)

/-- 概要：右移動 prism の通常の join への成分。
方針：pullback の第一射影の計算則。
規約：raw な射の等式。
使われ方：四境界の第一成分の照合。 -/
lemma kanRelativeJoinRightShiftPrism_fst {A B K C : SSet.{u}} (δ : K ⟶ C) (b : B ⟶ K)
    (H : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join A B ⟶ C) (hB : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr A B ≫ H = b ≫ δ) :
    kanRelativeJoinRightShiftPrism δ b H hB ≫ pullback.fst (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 C) δ) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.joinDiagonal C) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinRightShiftPrism A B ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap H b := pullback.lift_fst _ _ _

/-- 概要：右移動 prism の区間付き係数。
方針：pullback の第二射影の計算則。
規約：係数 H は元の時間によらない図式。
使われ方：四境界の第二成分の照合。 -/
lemma kanRelativeJoinRightShiftPrism_snd {A B K C : SSet.{u}} (δ : K ⟶ C) (b : B ⟶ K)
    (H : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join A B ⟶ C) (hB : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr A B ≫ H = b ≫ δ) :
    kanRelativeJoinRightShiftPrism δ b H hB ≫ pullback.snd (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 C) δ) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.joinDiagonal C) =
      lift (kanJoinRightShiftTime A B) (fst (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join A B) (Δ[1] : SSet.{u}) ≫ H) :=
  pullback.lift_snd _ _ _

/-- 概要：持ち上げた右 prism の始点は係数図式の左端への包含。
方針：始端の左包含と零の時間を二つの射影で計算する。
規約：H を全単体で保持する。
使われ方：右輸送の標準比較錐の回収。 -/
lemma kanRelativeJoinRightShiftPrism_zero {A B K C : SSet.{u}} (δ : K ⟶ C) (b : B ⟶ K)
    (H : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join A B ⟶ C) (hB : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr A B ≫ H = b ≫ δ) :
    SSet.ι₀ ≫ kanRelativeJoinRightShiftPrism δ b H hB =
      H ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinInl (𝟙 C) δ := by
  apply pullback.hom_ext
  · rw [Category.assoc, kanRelativeJoinRightShiftPrism_fst, ← Category.assoc,
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinRightShiftPrism_zero, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl_joinMap, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinInl_fst]
  · rw [Category.assoc, kanRelativeJoinRightShiftPrism_snd]
    simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinInl, Category.assoc, pullback.lift_snd, Category.id_comp]
    apply CartesianMonoidalCategory.hom_ext
    · simp only [Category.assoc, lift_fst, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint, SSet.comp_const]
      exact kanJoinRightShiftTime_zero A B
    · simp only [Category.assoc, lift_snd, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint]
      rfl

/-- 概要：持ち上げた右 prism の終点は元の局所図式の標準持ち上げ。
方針：二つの射影で終端と元の切断の式を使う。
規約：自然同型でなく射の等式。
使われ方：局所錐と右輸送の終点の同定。 -/
lemma kanRelativeJoinRightShiftPrism_one {A B K C : SSet.{u}} (δ : K ⟶ C) (b : B ⟶ K)
    (H : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join A B ⟶ C) (hB : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr A B ≫ H = b ≫ δ) :
    SSet.ι₁ ≫ kanRelativeJoinRightShiftPrism δ b H hB =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeJoinLift (𝟙 C) δ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl A B ≫ H) b H
        (by rw [Category.comp_id]) hB := by
  apply pullback.hom_ext
  · rw [Category.assoc, kanRelativeJoinRightShiftPrism_fst, ← Category.assoc,
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinRightShiftPrism_one, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap_comp, Category.id_comp, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeJoinLift_fst]
  · rw [Category.assoc, kanRelativeJoinRightShiftPrism_snd, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeJoinLift_snd]
    apply CartesianMonoidalCategory.hom_ext
    · rw [Category.assoc, lift_fst, lift_fst, kanJoinRightShiftTime_one]
    · simp only [Category.assoc, lift_snd]
      rfl

/-- 概要：持ち上げた右 prism の左境界は時間に定値な左端の図式。
方針：左境界の固定と零の時間を二つの射影で照合する。
規約：A=Δ⁰ の場合に頂点固定の条件になる。
使われ方：右輸送の fixedVertex フィールド。 -/
lemma kanRelativeJoinRightShiftPrism_left {A B K C : SSet.{u}} (δ : K ⟶ C) (b : B ⟶ K)
    (H : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join A B ⟶ C) (hB : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr A B ≫ H = b ≫ δ) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl A B ▷ (Δ[1] : SSet.{u})) ≫ kanRelativeJoinRightShiftPrism δ b H hB =
      fst A Δ[1] ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl A B ≫ H ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinInl (𝟙 C) δ := by
  apply pullback.hom_ext
  · rw [Category.assoc, kanRelativeJoinRightShiftPrism_fst, ← Category.assoc,
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinRightShiftPrism_left]
    simp only [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl_joinMap, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinInl_fst]
  · rw [Category.assoc, kanRelativeJoinRightShiftPrism_snd]
    simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinInl, Category.assoc, pullback.lift_snd, Category.id_comp]
    apply CartesianMonoidalCategory.hom_ext
    · simp only [Category.assoc, lift_fst, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint, SSet.comp_const]
      exact kanJoinRightShiftTime_left A B
    · simp only [Category.assoc, lift_snd, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint, Category.comp_id,
        whiskerRight_fst_assoc]

/-- 概要：持ち上げた右 prism の右境界は b に沿う標準右 prism。
方針：対角の自然性と H の右端の等式を両射影で使う。
規約：右端の自然変換を全時間で保持する。
使われ方：右輸送の diagram フィールド。 -/
lemma kanRelativeJoinRightShiftPrism_right {A B K C : SSet.{u}} (δ : K ⟶ C) (b : B ⟶ K)
    (H : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join A B ⟶ C) (hB : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr A B ≫ H = b ≫ δ) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr A B ▷ (Δ[1] : SSet.{u})) ≫ kanRelativeJoinRightShiftPrism δ b H hB =
      (b ▷ (Δ[1] : SSet.{u})) ≫ kanRelativeJoinRightPrism δ := by
  apply pullback.hom_ext
  · rw [Category.assoc, kanRelativeJoinRightShiftPrism_fst, ← Category.assoc,
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinRightShiftPrism_right]
    simp only [kanRelativeJoinRightPrism, Category.assoc, pullback.lift_fst]
    rw [← Category.assoc (b ▷ (Δ[1] : SSet.{u})),
      BraidedCategory.braiding_naturality_left, Category.assoc,
      ← Category.assoc ((Δ[1] : SSet.{u}) ◁ b), _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.joinDiagonal_naturality]
    simp only [Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap_comp, Category.id_comp, Category.comp_id, hB]
  · rw [Category.assoc, kanRelativeJoinRightShiftPrism_snd]
    simp only [kanRelativeJoinRightPrism, Category.assoc, pullback.lift_snd]
    apply CartesianMonoidalCategory.hom_ext
    · simp only [Category.assoc, lift_fst]
      change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr A B ▷ (Δ[1] : SSet.{u})) ≫ kanJoinRightShiftTime A B = snd B Δ[1]
      exact kanJoinRightShiftTime_right A B
    · simp only [Category.assoc, lift_snd, whiskerRight_fst_assoc]
      rw [hB]
      rfl

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions
