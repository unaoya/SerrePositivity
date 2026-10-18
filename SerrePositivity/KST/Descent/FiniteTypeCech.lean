module

public import SerrePositivity.KST.Descent.FiniteTypeLimits
public import SerrePositivity.KST.Descent.SplitCech

/-!
# 元の有限型の圏内の Čech 各段と分裂

## 概要
実際の Čech nerve の各非増強段で元の射を底変換すると、実際の切断を持つ。

## 方針
Noether 基底上の有限極限を使い、各段の零番目の射影を持ち上げに使う。

## 規約
図式と切断は前層の元の定義域内に構成する。通常の極限を Tot と呼ばない。

## 使われ方
論文 補題 3.2 の τ 位相の層論を分裂降下・Fubini・細分の Čech 計算に置換する入力。
-/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace SerrePositivity.KST.Descent

variable {S : Scheme.{u}} [IsNoetherian S] {X Y : FiniteTypeSchemes S} (f : X ⟶ Y)

/-- 概要：元の有限型の圏内の実際の増強 Čech nerve（論文 補題 3.2）。
方針：構成した有限極限で Mathlib の Čech nerve を作る。
規約：前層の定義域を全スキームの圏へ交換しない。
使われ方：元の前層による余単体図式。 -/
noncomputable def finiteTypeAugmentedCech : SimplicialObject.Augmented (FiniteTypeSchemes S) :=
  (Arrow.mk f).augmentedCechNerve

/-- 概要：実際の Čech 各段上に引き戻した元の射（論文 補題 3.2）。
方針：増強射の各成分で元の射を底変換する。
規約：非増強の各段のみを対象とし、増強先 Y では切断を仮定しない。
使われ方：段ごとの切断つき降下。 -/
noncomputable def finiteTypeCechStageArrow (n : SimplexCategoryᵒᵖ) :
    Arrow (FiniteTypeSchemes S) :=
  Arrow.mk (pullback.snd f ((finiteTypeAugmentedCech f).hom.app n))

/-- 概要：Čech 各段での底変換を実際の関手に束ねる（論文 補題 3.2）。
方針：元の Čech の射と引き戻しの map から Arrow の射を構成する。
規約：零番目の射影から選んだ切断の自然性は要求しない。
使われ方：Fubini に供給する二重 Čech 図式。 -/
noncomputable def finiteTypeCechBaseChange : SimplexCategoryᵒᵖ ⥤ Arrow (FiniteTypeSchemes S) where
  obj := finiteTypeCechStageArrow f
  map {n m} α := Arrow.homMk
    (pullback.map f ((finiteTypeAugmentedCech f).hom.app n)
      f ((finiteTypeAugmentedCech f).hom.app m) (𝟙 X)
      ((finiteTypeAugmentedCech f).left.map α) (𝟙 Y) (by simp)
      (by exact ((finiteTypeAugmentedCech f).hom.naturality α).symm))
    ((finiteTypeAugmentedCech f).left.map α) (by
      change pullback.map _ _ _ _ _ _ _ _ _ ≫ pullback.snd _ _ =
        pullback.snd _ _ ≫ _
      exact pullback.lift_snd _ _ _)
  map_id n := by
    apply Arrow.hom_ext
    · change pullback.map f ((finiteTypeAugmentedCech f).hom.app n)
        f ((finiteTypeAugmentedCech f).hom.app n) (𝟙 X)
        ((finiteTypeAugmentedCech f).left.map (𝟙 n)) (𝟙 Y) (by simp)
        ((finiteTypeAugmentedCech f).hom.naturality (𝟙 n)).symm = 𝟙 _
      apply pullback.hom_ext
      · exact (pullback.lift_fst _ _ _).trans
          ((Category.comp_id _).trans (Category.id_comp _).symm)
      · exact (pullback.lift_snd _ _ _).trans
          ((congrArg (fun k ↦ pullback.snd f ((finiteTypeAugmentedCech f).hom.app n) ≫ k)
            ((finiteTypeAugmentedCech f).left.map_id n)).trans
            ((Category.comp_id _).trans (Category.id_comp _).symm))
    · exact (finiteTypeAugmentedCech f).left.map_id n
  map_comp α β := by
    apply Arrow.hom_ext
    · apply pullback.hom_ext <;>
        simp [finiteTypeCechStageArrow, pullback.map, PullbackCone.mk]
    · exact (finiteTypeAugmentedCech f).left.map_comp α β

/-- 概要：元の有限型の圏内の二重の増強 Čech 図式（論文 補題 3.2）。
方針：各段の底変換の Arrow の関手に増強 Čech nerve 関手を合成する。
規約：全ての面射・退化射の可換性を関手の法則に保持する。
使われ方：Tot の Fubini と段ごとの分裂降下を接続する実際の図式。 -/
noncomputable def finiteTypeDoubleCech :
    SimplexCategoryᵒᵖ ⥤ SimplicialObject.Augmented (FiniteTypeSchemes S) :=
  finiteTypeCechBaseChange f ⋙ SimplicialObject.augmentedCechNerve

/-- 概要：Čech 各段で底変換した射は実際に分裂する（論文 補題 3.2）。
方針：各段の零番目の射影と恒等射を引き戻しへ持ち上げる。
規約：段ごとの切断の選択であり、全ての単体射との自然性は主張しない。
使われ方：各段での軌道帰納と分裂降下。 -/
noncomputable def finiteTypeCechStageSplitEpi (n : SimplexCategoryᵒᵖ) :
    SplitEpi (finiteTypeCechStageArrow f n).hom :=
  baseChangeSplitEpi f ((finiteTypeAugmentedCech f).hom.app n)
    (WidePullback.π (fun _ : Fin (n.unop.len + 1) ↦ f) 0) (WidePullback.π_arrow _ _)

/-- 概要：Čech 各段での底変換の実際の Čech nerve の分裂（論文 補題 3.2）。
方針：構成した切断から全次数の extra degeneracy を得る。
規約：面射・退化射の恒等式を含み、単なる各段の群の分裂ではない。
使われ方：Tot の分裂降下へ渡す幾何データ。 -/
noncomputable def finiteTypeCechStageExtraDegeneracy (n : SimplexCategoryᵒᵖ) :
    SimplicialObject.Augmented.ExtraDegeneracy
      (finiteTypeCechStageArrow f n).augmentedCechNerve :=
  Arrow.AugmentedCechNerve.extraDegeneracy _ (finiteTypeCechStageSplitEpi f n)

variable {V : Type v} [Category.{w} V]

/-- 概要：元の前層を二重 Čech 図式全体に適用する（論文 補題 3.2）。
方針：各段だけでなく外側の全ての単体射も同じ反変関手で写す。
規約：V の反対圏の二重単体図式として記述し、各次数の通常の極限を使わない。
使われ方：Tot と引き戻しの Fubini に供給する実際の余単体図式。 -/
noncomputable def finiteTypeDoubleCechImage (F : (FiniteTypeSchemes S)ᵒᵖ ⥤ V) :
    SimplexCategoryᵒᵖ ⥤ SimplicialObject.Augmented Vᵒᵖ :=
  finiteTypeDoubleCech f ⋙ (SimplicialObject.Augmented.whiskering _ Vᵒᵖ).obj F.rightOp

/-- 概要：同じ前層の Čech 各段の底変換への像（論文 補題 3.2）。
方針：反対圏への関手として元の前層を実際の増強図式に適用する。
規約：Tot の構成や降下そのものを定義してはいない。
使われ方：分裂降下と Fubini の接続先。 -/
noncomputable def finiteTypeCechStageImage (F : (FiniteTypeSchemes S)ᵒᵖ ⥤ V)
    (n : SimplexCategoryᵒᵖ) : SimplicialObject.Augmented Vᵒᵖ :=
  ((SimplicialObject.Augmented.whiskering _ Vᵒᵖ).obj F.rightOp).obj
    (finiteTypeCechStageArrow f n).augmentedCechNerve

/-- 概要：元の前層の各段の像も実際の余単体分裂を持つ（論文 補題 3.2）。
方針：構成した extra degeneracy と全恒等式を元の前層で写す。
規約：反対圏の単体対象で余単体分裂を表す。
使われ方：実際の Tot のホモトピー不変性に供給する入力。 -/
noncomputable def finiteTypeCechStageImageExtraDegeneracy
    (F : (FiniteTypeSchemes S)ᵒᵖ ⥤ V) (n : SimplexCategoryᵒᵖ) :
    SimplicialObject.Augmented.ExtraDegeneracy (finiteTypeCechStageImage f F n) :=
  (finiteTypeCechStageExtraDegeneracy f n).map F.rightOp

end SerrePositivity.KST.Descent
