module

public import SerrePositivity.InfinityCategories.F1B.Joins.JoinRightShiftCoefficient
public import SerrePositivity.InfinityCategories.F1B.KanExtension.RelativeJoinLocalCone

/-!
概要：右移動 prism の relative join への持ち上げ。
方針：係数の可換性を pullback 条件とし、四境界を両射影で比較する。
規約：時間は第二因子、δ の単射性や quasicategory 性は不要。
使われ方：右 Kan 拡張の局所比較錐と指定変換の輸送の接続。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：右移動後の join の切断を区間として読む。
方針：右移動 prism に区間射影を後合成する。
規約：元の時間と元の join の時間をまとめる。
使われ方：右 relative join の係数の区間成分。 -/
def kanJoinRightShiftTime (A B : SSet.{u}) :
    join A B ⊗ (Δ[1] : SSet.{u}) ⟶ (Δ[1] : SSet.{u}) :=
  SerrePositivity.InfinityCategories.joinRightShiftPrism A B ≫ joinIntervalProjection (join A B) B

/-- 概要：右移動の始点の時間は零に定値。
方針：始点が左包含であることを使う。
規約：全単体での射の等式。
使われ方：右輸送の start 条件。 -/
lemma kanJoinRightShiftTime_zero (A B : SSet.{u}) :
    SSet.ι₀ ≫ kanJoinRightShiftTime A B =
      SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) := by
  rw [kanJoinRightShiftTime, ← Category.assoc, SerrePositivity.InfinityCategories.joinRightShiftPrism_zero,
    joinIntervalProjection_inl]

/-- 概要：右移動の終点の時間は元の join の時間。
方針：終点の joinMap と区間射影の自然性。
規約：元の切断を保持する。
使われ方：局所比較錐の回収。 -/
lemma kanJoinRightShiftTime_one (A B : SSet.{u}) :
    SSet.ι₁ ≫ kanJoinRightShiftTime A B = joinIntervalProjection A B := by
  rw [kanJoinRightShiftTime, ← Category.assoc, SerrePositivity.InfinityCategories.joinRightShiftPrism_one,
    joinIntervalProjection_naturality]

/-- 概要：右移動の左境界の時間は零に定値。
方針：左因子の固定と左包含の時間を計算する。
規約：全時刻で同じ左端にある。
使われ方：右輸送の fixedVertex 条件。 -/
lemma kanJoinRightShiftTime_left (A B : SSet.{u}) :
    (joinInl A B ▷ (Δ[1] : SSet.{u})) ≫ kanJoinRightShiftTime A B =
      SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) := by
  rw [kanJoinRightShiftTime, ← Category.assoc, SerrePositivity.InfinityCategories.joinRightShiftPrism_left,
    Category.assoc, Category.assoc, joinIntervalProjection_inl,
    SSet.comp_const, SSet.comp_const]

/-- 概要：右移動の右境界の時間は元の prism の時間。
方針：区間付き対角の時間と braiding の射影を計算する。
規約：第二因子が時間。
使われ方：右輸送の diagram 条件。 -/
lemma kanJoinRightShiftTime_right (A B : SSet.{u}) :
    (joinInr A B ▷ (Δ[1] : SSet.{u})) ≫ kanJoinRightShiftTime A B = snd B Δ[1] := by
  rw [kanJoinRightShiftTime, ← Category.assoc, SerrePositivity.InfinityCategories.joinRightShiftPrism_right,
    Category.assoc, Category.assoc, joinIntervalProjection_naturality,
    joinDiagonal_joinIntervalProjection]
  rfl

/-- 概要：右 relative join の標準指定変換の prism。
方針：右因子の対角を δ と恒等射で写し、底の区間付き δ と合わせる。
規約：始点は δ に沿う左包含、終点は右包含。
使われ方：右 Kan 拡張の指定自然変換。 -/
def kanRelativeJoinRightPrism {K C : SSet.{u}} (δ : K ⟶ C) :
    K ⊗ (Δ[1] : SSet.{u}) ⟶ relativeJoin (𝟙 C) δ :=
  pullback.lift
    ((β_ K (Δ[1] : SSet.{u})).hom ≫ joinDiagonal K ≫ joinMap δ (𝟙 K))
    ((β_ K (Δ[1] : SSet.{u})).hom ≫ ((Δ[1] : SSet.{u}) ◁ δ)) (by
      simp only [Category.assoc, ← joinMap_comp, Category.comp_id,
        Category.id_comp, ← joinDiagonal_naturality])

/-- 概要：標準右 prism の始点は δ に沿う左端。
方針：対角の始点を両射影で比較する。
規約：時刻零。
使われ方：右指定変換の始点。 -/
lemma kanRelativeJoinRightPrism_zero {K C : SSet.{u}} (δ : K ⟶ C) :
    SSet.ι₀ ≫ kanRelativeJoinRightPrism δ = δ ≫ relativeJoinInl (𝟙 C) δ := by
  apply pullback.hom_ext
  · simp only [kanRelativeJoinRightPrism, Category.assoc, pullback.lift_fst,
      relativeJoinInl_fst]
    change prismEndpoint 0 K ≫ joinDiagonal K ≫ joinMap δ (𝟙 K) = _
    rw [← Category.assoc, prismEndpoint_zero_joinDiagonal, joinInl_joinMap]
  · simp only [kanRelativeJoinRightPrism, relativeJoinInl, Category.assoc,
      pullback.lift_snd, Category.id_comp]
    rfl

/-- 概要：標準右 prism の終点は右端。
方針：対角の終点を両射影で比較する。
規約：時刻一。
使われ方：右指定変換の終点。 -/
lemma kanRelativeJoinRightPrism_one {K C : SSet.{u}} (δ : K ⟶ C) :
    SSet.ι₁ ≫ kanRelativeJoinRightPrism δ = relativeJoinInr (𝟙 C) δ := by
  apply pullback.hom_ext
  · simp only [kanRelativeJoinRightPrism, Category.assoc, pullback.lift_fst,
      relativeJoinInr_fst]
    change prismEndpoint 1 K ≫ joinDiagonal K ≫ joinMap δ (𝟙 K) = _
    rw [← Category.assoc, prismEndpoint_one_joinDiagonal, joinInr_joinMap, Category.id_comp]
  · simp only [kanRelativeJoinRightPrism, relativeJoinInr, Category.assoc,
      pullback.lift_snd]
    rfl

/-- 概要：左端の係数図式から元の局所図式へ移す右 relative join の prism。
方針：右移動 prism の左右を H と b で写し、元の H を係数に使う。
規約：右端で H が b≫δ に一致することだけを仮定する。
使われ方：右比較錐の実際の輸送。 -/
def kanRelativeJoinRightShiftPrism {A B K C : SSet.{u}} (δ : K ⟶ C) (b : B ⟶ K)
    (H : join A B ⟶ C) (hB : joinInr A B ≫ H = b ≫ δ) :
    join A B ⊗ (Δ[1] : SSet.{u}) ⟶ relativeJoin (𝟙 C) δ :=
  pullback.lift (SerrePositivity.InfinityCategories.joinRightShiftPrism A B ≫ joinMap H b)
    (lift (kanJoinRightShiftTime A B) (fst (join A B) (Δ[1] : SSet.{u}) ≫ H)) (by
      have h : joinMap H b ≫ joinMap (𝟙 C) δ =
          joinMap (𝟙 (join A B)) (joinInr A B) ≫ joinMap H H := by
        rw [← joinMap_comp, Category.comp_id, ← hB, ← joinMap_comp, Category.id_comp]
      rw [Category.assoc, h, ← Category.assoc, SerrePositivity.InfinityCategories.joinRightShiftPrism_coefficient,
        Category.assoc, ← joinDiagonal_naturality, ← Category.assoc]
      rfl)

/-- 概要：右移動 prism の通常の join への成分。
方針：pullback の第一射影の計算則。
規約：raw な射の等式。
使われ方：四境界の第一成分の照合。 -/
lemma kanRelativeJoinRightShiftPrism_fst {A B K C : SSet.{u}} (δ : K ⟶ C) (b : B ⟶ K)
    (H : join A B ⟶ C) (hB : joinInr A B ≫ H = b ≫ δ) :
    kanRelativeJoinRightShiftPrism δ b H hB ≫ pullback.fst (joinMap (𝟙 C) δ) (joinDiagonal C) =
      SerrePositivity.InfinityCategories.joinRightShiftPrism A B ≫ joinMap H b := pullback.lift_fst _ _ _

/-- 概要：右移動 prism の区間付き係数。
方針：pullback の第二射影の計算則。
規約：係数 H は元の時間によらない図式。
使われ方：四境界の第二成分の照合。 -/
lemma kanRelativeJoinRightShiftPrism_snd {A B K C : SSet.{u}} (δ : K ⟶ C) (b : B ⟶ K)
    (H : join A B ⟶ C) (hB : joinInr A B ≫ H = b ≫ δ) :
    kanRelativeJoinRightShiftPrism δ b H hB ≫ pullback.snd (joinMap (𝟙 C) δ) (joinDiagonal C) =
      lift (kanJoinRightShiftTime A B) (fst (join A B) (Δ[1] : SSet.{u}) ≫ H) :=
  pullback.lift_snd _ _ _

/-- 概要：持ち上げた右 prism の始点は係数図式の左端への包含。
方針：始端の左包含と零の時間を二つの射影で計算する。
規約：H を全単体で保持する。
使われ方：右輸送の標準比較錐の回収。 -/
lemma kanRelativeJoinRightShiftPrism_zero {A B K C : SSet.{u}} (δ : K ⟶ C) (b : B ⟶ K)
    (H : join A B ⟶ C) (hB : joinInr A B ≫ H = b ≫ δ) :
    SSet.ι₀ ≫ kanRelativeJoinRightShiftPrism δ b H hB =
      H ≫ relativeJoinInl (𝟙 C) δ := by
  apply pullback.hom_ext
  · rw [Category.assoc, kanRelativeJoinRightShiftPrism_fst, ← Category.assoc,
      SerrePositivity.InfinityCategories.joinRightShiftPrism_zero, joinInl_joinMap, Category.assoc, relativeJoinInl_fst]
  · rw [Category.assoc, kanRelativeJoinRightShiftPrism_snd]
    simp only [relativeJoinInl, Category.assoc, pullback.lift_snd, Category.id_comp]
    apply CartesianMonoidalCategory.hom_ext
    · simp only [Category.assoc, lift_fst, prismEndpoint, SSet.comp_const]
      exact kanJoinRightShiftTime_zero A B
    · simp only [Category.assoc, lift_snd, prismEndpoint]
      rfl

/-- 概要：持ち上げた右 prism の終点は元の局所図式の標準持ち上げ。
方針：二つの射影で終端と元の切断の式を使う。
規約：自然同型でなく射の等式。
使われ方：局所錐と右輸送の終点の同定。 -/
lemma kanRelativeJoinRightShiftPrism_one {A B K C : SSet.{u}} (δ : K ⟶ C) (b : B ⟶ K)
    (H : join A B ⟶ C) (hB : joinInr A B ≫ H = b ≫ δ) :
    SSet.ι₁ ≫ kanRelativeJoinRightShiftPrism δ b H hB =
      kanRelativeJoinLift (𝟙 C) δ (joinInl A B ≫ H) b H
        (by rw [Category.comp_id]) hB := by
  apply pullback.hom_ext
  · rw [Category.assoc, kanRelativeJoinRightShiftPrism_fst, ← Category.assoc,
      SerrePositivity.InfinityCategories.joinRightShiftPrism_one, ← joinMap_comp, Category.id_comp, kanRelativeJoinLift_fst]
  · rw [Category.assoc, kanRelativeJoinRightShiftPrism_snd, kanRelativeJoinLift_snd]
    apply CartesianMonoidalCategory.hom_ext
    · rw [Category.assoc, lift_fst, lift_fst, kanJoinRightShiftTime_one]
    · simp only [Category.assoc, lift_snd]
      rfl

/-- 概要：持ち上げた右 prism の左境界は時間に定値な左端の図式。
方針：左境界の固定と零の時間を二つの射影で照合する。
規約：A=Δ⁰ の場合に頂点固定の条件になる。
使われ方：右輸送の fixedVertex フィールド。 -/
lemma kanRelativeJoinRightShiftPrism_left {A B K C : SSet.{u}} (δ : K ⟶ C) (b : B ⟶ K)
    (H : join A B ⟶ C) (hB : joinInr A B ≫ H = b ≫ δ) :
    (joinInl A B ▷ (Δ[1] : SSet.{u})) ≫ kanRelativeJoinRightShiftPrism δ b H hB =
      fst A Δ[1] ≫ joinInl A B ≫ H ≫ relativeJoinInl (𝟙 C) δ := by
  apply pullback.hom_ext
  · rw [Category.assoc, kanRelativeJoinRightShiftPrism_fst, ← Category.assoc,
      SerrePositivity.InfinityCategories.joinRightShiftPrism_left]
    simp only [Category.assoc, joinInl_joinMap, relativeJoinInl_fst]
  · rw [Category.assoc, kanRelativeJoinRightShiftPrism_snd]
    simp only [relativeJoinInl, Category.assoc, pullback.lift_snd, Category.id_comp]
    apply CartesianMonoidalCategory.hom_ext
    · simp only [Category.assoc, lift_fst, prismEndpoint, SSet.comp_const]
      exact kanJoinRightShiftTime_left A B
    · simp only [Category.assoc, lift_snd, prismEndpoint, Category.comp_id,
        whiskerRight_fst_assoc]

/-- 概要：持ち上げた右 prism の右境界は b に沿う標準右 prism。
方針：対角の自然性と H の右端の等式を両射影で使う。
規約：右端の自然変換を全時間で保持する。
使われ方：右輸送の diagram フィールド。 -/
lemma kanRelativeJoinRightShiftPrism_right {A B K C : SSet.{u}} (δ : K ⟶ C) (b : B ⟶ K)
    (H : join A B ⟶ C) (hB : joinInr A B ≫ H = b ≫ δ) :
    (joinInr A B ▷ (Δ[1] : SSet.{u})) ≫ kanRelativeJoinRightShiftPrism δ b H hB =
      (b ▷ (Δ[1] : SSet.{u})) ≫ kanRelativeJoinRightPrism δ := by
  apply pullback.hom_ext
  · rw [Category.assoc, kanRelativeJoinRightShiftPrism_fst, ← Category.assoc,
      SerrePositivity.InfinityCategories.joinRightShiftPrism_right]
    simp only [kanRelativeJoinRightPrism, Category.assoc, pullback.lift_fst]
    rw [← Category.assoc (b ▷ (Δ[1] : SSet.{u})),
      BraidedCategory.braiding_naturality_left, Category.assoc,
      ← Category.assoc ((Δ[1] : SSet.{u}) ◁ b), joinDiagonal_naturality]
    simp only [Category.assoc, ← joinMap_comp, Category.id_comp, Category.comp_id, hB]
  · rw [Category.assoc, kanRelativeJoinRightShiftPrism_snd]
    simp only [kanRelativeJoinRightPrism, Category.assoc, pullback.lift_snd]
    apply CartesianMonoidalCategory.hom_ext
    · simp only [Category.assoc, lift_fst]
      change (joinInr A B ▷ (Δ[1] : SSet.{u})) ≫ kanJoinRightShiftTime A B = snd B Δ[1]
      exact kanJoinRightShiftTime_right A B
    · simp only [Category.assoc, lift_snd, whiskerRight_fst_assoc]
      rw [hB]
      rfl

end SerrePositivity.InfinityCategories
