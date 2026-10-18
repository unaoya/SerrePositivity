module

public import SerrePositivity.KST.Descent.CechBaseChangeOver

/-!
# 全次数観測後の transfer の正規化

## 概要
元の値域の線形性を要求せず、実際の図式関手と観測関手で写した後の rank 公式を使う。

## 方針
pullback と transfer の合成が比較の両端で同型なら、矢の圏でその逆を用いて retract を作る。

## 規約
rank 公式は実際の図式関手を適用した後の公式。π_* と Tot の交換は仮定しない。

## 使われ方
論文 補題 3.2 の transfer 還元を、L9 の元のスペクトル圏の有理線形性なしで接続する。
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Linear Opposite

namespace SerrePositivity.KST.Descent

/-- 概要：合成が同型となる往復の射から retract を作る（論文 補題 3.2）。
方針：戻る射に往復の合成の逆を合成する。
規約：圏の加法性・線形性は不要。
使われ方：観測後に同型と分かる rank 合成の正規化。 -/
noncomputable def invertibleCompositeRetract {D : Type*} [Category* D] {A B : D}
    (i : A ⟶ B) (r : B ⟶ A) [IsIso (i ≫ r)] : Retract A B where
  i := i
  r := r ≫ inv (i ≫ r)
  retract := (Category.assoc _ _ _).symm.trans (IsIso.hom_inv_id (i ≫ r))

/-- 概要：比較の両端で往復の合成が同型なら比較射の retract を得る（論文 補題 3.2）。
方針：自然性で往復の矢を作り、その合成を矢の圏で逆にする。
規約：元の図式の圏に線形性を要求しない。
使われ方：実際の Tot・観測の像で transfer を正規化する。 -/
noncomputable def naturalComparisonRetractOfIsoComposite
    {D V : Type*} [Category* D] [Category* V]
    (source target : D ⥤ V) (comparison : source ⟶ target)
    {A B : D} (i : A ⟶ B) (r : B ⟶ A)
    [IsIso (source.map (i ≫ r))] [IsIso (target.map (i ≫ r))] :
    RetractArrow (comparison.app A) (comparison.app B) := by
  let ai : Arrow.mk (comparison.app A) ⟶ Arrow.mk (comparison.app B) :=
    Arrow.homMk (source.map i) (target.map i) (comparison.naturality i)
  let ar : Arrow.mk (comparison.app B) ⟶ Arrow.mk (comparison.app A) :=
    Arrow.homMk (source.map r) (target.map r) (comparison.naturality r)
  haveI : IsIso ((ai ≫ ar).left) := by
    change IsIso (source.map i ≫ source.map r)
    rw [← source.map_comp]
    infer_instance
  haveI : IsIso ((ai ≫ ar).right) := by
    change IsIso (target.map i ≫ target.map r)
    rw [← target.map_comp]
    infer_instance
  haveI := Arrow.isIso_of_isIso_left_of_isIso_right (ai ≫ ar)
  exact invertibleCompositeRetract ai ar

/-- 概要：往復の合成の観測後の全次数同型から降下比較を移す（論文 補題 3.2）。
方針：整数次数ごとに観測後の比較の矢の圏で retract を構成する。
規約：元の値域で rank の逆数を掛ける操作は使わない。
使われ方：有理化された π_* の rank 合成を用いる transfer 還元。 -/
theorem piComparison_of_observedComposite
    {D V : Type*} [Category* D] [Category* V]
    (observation : ℤ → V ⥤ ModuleCat ℚ)
    (source target : D ⥤ V) (comparison : source ⟶ target)
    {A B : D} (i : A ⟶ B) (r : B ⟶ A)
    (sourceComposite : piIsomorphisms observation (source.map (i ≫ r)))
    (targetComposite : piIsomorphisms observation (target.map (i ≫ r)))
    (hB : piIsomorphisms observation (comparison.app B)) :
    piIsomorphisms observation (comparison.app A) := by
  intro n
  have : IsIso ((source ⋙ observation n).map (i ≫ r)) := sourceComposite n
  have : IsIso ((target ⋙ observation n).map (i ≫ r)) := targetComposite n
  let h := naturalComparisonRetractOfIsoComposite
    (source ⋙ observation n) (target ⋙ observation n)
    (Functor.whiskerRight comparison (observation n)) i r
  exact MorphismProperty.of_retract (P := MorphismProperty.isomorphisms _) h (hB n)

/-- 概要：有理線形圏で正の整数倍の恒等射は同型（論文 補題 3.2）。
方針：逆数倍の恒等射を逆射として明示する。
規約：線形性を使うのはこの観測先の圏だけ。
使われ方：観測後の局所 rank 公式から合成の同型性を得る。 -/
theorem isIso_positiveRankIdentity {V : Type*} [Category* V]
    [Preadditive V] [Linear ℚ V] (A : V) (rank : ℕ) (positive : 0 < rank) :
    IsIso ((rank : ℚ) • 𝟙 A) := by
  have hn : (rank : ℚ) ≠ 0 := by exact_mod_cast positive.ne'
  refine ⟨⟨(rank : ℚ)⁻¹ • 𝟙 A, ?_, ?_⟩⟩
  · simp [smul_smul, hn]
  · simp [smul_smul, hn]

/-- 概要：観測後の両端の局所 rank 公式による全次数降下の移行（論文 補題 3.2）。
方針：正の rank 倍は有理加群の圏で同型なので、観測後の合成による retract を使う。
規約：元の圏の線形性は不要。公式は source・target の実際の像で要求する。
使われ方：π_* と Tot の交換を用いない transfer の正規化。 -/
theorem piComparison_of_observedRank
    {D V : Type*} [Category* D] [Category* V]
    (observation : ℤ → V ⥤ ModuleCat ℚ)
    (source target : D ⥤ V) (comparison : source ⟶ target)
    {A B : D} (i : A ⟶ B) (r : B ⟶ A)
    (rank : ℕ) (positive : 0 < rank)
    (sourceRank : ∀ n, (observation n).map (source.map (i ≫ r)) =
      (rank : ℚ) • 𝟙 ((observation n).obj (source.obj A)))
    (targetRank : ∀ n, (observation n).map (target.map (i ≫ r)) =
      (rank : ℚ) • 𝟙 ((observation n).obj (target.obj A)))
    (hB : piIsomorphisms observation (comparison.app B)) :
    piIsomorphisms observation (comparison.app A) := by
  apply piComparison_of_observedComposite observation source target comparison i r
  · intro n
    rw [sourceRank n]
    exact isIso_positiveRankIdentity _ rank positive
  · intro n
    rw [targetRank n]
    exact isIso_positiveRankIdentity _ rank positive
  · exact hB

section Cech

universe u v w t

variable {C : Type u} [Category.{v} C] [HasFiniteLimits C]
  {V : Type w} [Category.{t} V] {D : Type*} [Category* D]
  {W X Y : C} (cover : W ⟶ Y)
  (total : ((SimplexCategoryᵒᵖ)ᵒᵖ ⥤ V) ⥤ D)

/-- 概要：Čech 増強先の定数図式を実際の図式関手で写す（論文 補題 3.2）。
方針：元の増強先の評価・定数図式関手と指定関手を合成する。
規約：指定関手の実構成は引数として保持する。
使われ方：観測後の rank 公式を要求する比較の始域。 -/
def cechAugmentationTotalSource : ((Over Y)ᵒᵖ ⥤ V) ⥤ D :=
  presheafAugmentationSource (J := SimplexCategoryᵒᵖ) (Y := Y) ⋙ total

/-- 概要：Čech 図式への制限を実際の図式関手で写す（論文 補題 3.2）。
方針：Over の実際の Čech 図式の制限関手と指定関手を合成する。
規約：通常の極限を Tot として代用しない。
使われ方：観測後の rank 公式を要求する比較の終域。 -/
noncomputable def cechAugmentationTotalTarget : ((Over Y)ᵒᵖ ⥤ V) ⥤ D :=
  presheafAugmentationTarget (cechOverDiagram cover) ⋙ total

/-- 概要：実際の図式関手で写した指定 Čech 増強の自然比較（論文 補題 3.2）。
方針：前層について自然な増強比較に指定関手を適用する。
規約：各前層での成分は指定増強の実際の像。
使われ方：元の値域の線形性を使わない観測後の transfer 還元。 -/
noncomputable def cechAugmentationTotalComparison :
    cechAugmentationTotalSource (Y := Y) total ⟶ cechAugmentationTotalTarget cover total :=
  Functor.whiskerRight (presheafAugmentationComparison (cechOverDiagram cover)) total

/-- 概要：観測後の局所 rank 公式と底変換被覆の降下から元の全次数比較を得る（補題 3.2）。
方針：実際の底変換被覆との増強同型で降下を移し、観測後の比較の矢の圏で正規化する。
規約：元の値域 V と図式関手の値域 D の線形性は不要。
二つの rank 公式は実際の図式関手の像で供給する条件であり、各段の公式から無証明で導かない。
使われ方：L9 の実際の Tot と π_* を接続するときの transfer 還元の界面。 -/
theorem BaseChangeTransfer.piCechComparison_of_observedRank
    (observation : ℤ → D ⥤ ModuleCat ℚ)
    {f : X ⟶ Y} {F : Cᵒᵖ ⥤ V} (tr : BaseChangeTransfer f F)
    (rank : ℕ) (positive : 0 < rank)
    (sourceRank : ∀ n, (observation n).map
        ((cechAugmentationTotalSource (Y := Y) total).map
          (baseChangePresheafPullback f F ≫ tr.transfer)) =
      (rank : ℚ) • 𝟙 ((observation n).obj
        ((cechAugmentationTotalSource (Y := Y) total).obj (overPresheaf (Y := Y) F))))
    (targetRank : ∀ n, (observation n).map
        ((cechAugmentationTotalTarget cover total).map
          (baseChangePresheafPullback f F ≫ tr.transfer)) =
      (rank : ℚ) • 𝟙 ((observation n).obj
        ((cechAugmentationTotalTarget cover total).obj (overPresheaf (Y := Y) F))))
    (baseChanged : piIsomorphisms observation
      (total.map (cechPresheafAugmentation (pullback.snd cover f) F))) :
    piIsomorphisms observation (total.map (cechPresheafAugmentation cover F)) := by
  have hBC : piIsomorphisms observation
      (total.map (cechBaseChangedAugmentation cover f F)) :=
    piIsomorphisms_of_retract observation
      (RetractArrow.map (Retract.ofIso (cechBaseChangeAugmentationIso cover f F)) total) baseChanged
  exact piComparison_of_observedRank observation
    (cechAugmentationTotalSource (Y := Y) total) (cechAugmentationTotalTarget cover total)
    (cechAugmentationTotalComparison cover total) (baseChangePresheafPullback f F) tr.transfer
    rank positive sourceRank targetRank hBC

end Cech

end SerrePositivity.KST.Descent
