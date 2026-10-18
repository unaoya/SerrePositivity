module

public import SerrePositivity.KST.Descent.CechBaseChange
public import SerrePositivity.KST.Descent.CechTransferRetract

/-!
# 底変換した Čech 図式と transfer の幾何図式の同型

## 概要
実際の底変換被覆の Čech nerve と、元の Čech 図式を Over で底変換した図式を同一視する。

## 方針
増強 Čech の Cartesian 性を各段で評価し、二射影の普遍性で自然性を検査する。

## 規約
全単体射と増強先への射を保持する。値域の Tot の同型性はここでは主張しない。

## 使われ方
論文 補題 3.2 の実際の分裂 Čech 図式と有限平坦 transfer 図式の接続。
-/

@[expose] public section

universe u v w t

open CategoryTheory CategoryTheory.Limits Opposite

namespace SerrePositivity.KST.Descent

variable {C : Type u} [Category.{v} C] [HasFiniteLimits C]
  {W X Y : C} (cover : W ⟶ Y) (f : X ⟶ Y)

/-- 概要：底変換被覆の Čech 各段と元の段の底変換の標準同型（論文 補題 3.2）。
方針：実際の増強 Čech の Cartesian 正方形を評価する。
規約：元の段への射と底変換基底への増強を二射影として保持する。
使われ方：図式全体の自然同型の成分。 -/
noncomputable def cechBaseChangeStageIso (n : SimplexCategoryᵒᵖ) :
    (Arrow.mk (pullback.snd cover f)).cechNerve.obj n ≅
      pullback ((Arrow.mk cover).augmentedCechNerve.hom.app n) f :=
  ((baseChangeCech_isPullback cover f).app n).isoPullback

/-- 概要：段の標準同型は元の Čech への比較を保つ（論文 補題 3.2）。
方針：Cartesian 正方形からの標準同型の第一射影公式を使う。
規約：指定された Arrow の比較射を保持する。
使われ方：全単体射についての自然性。 -/
theorem cechBaseChangeStageIso_hom_fst (n : SimplexCategoryᵒᵖ) :
    (cechBaseChangeStageIso cover f n).hom ≫
        pullback.fst ((Arrow.mk cover).augmentedCechNerve.hom.app n) f =
      (Arrow.mapCechNerve (baseChangeArrowToOriginal cover f)).app n :=
  ((baseChangeCech_isPullback cover f).app n).isoPullback_hom_fst

/-- 概要：段の標準同型は底変換基底への増強を保つ（論文 補題 3.2）。
方針：Cartesian 正方形からの標準同型の第二射影公式を使う。
規約：増強先は底変換基底 X。
使われ方：増強を含む図式の接続。 -/
theorem cechBaseChangeStageIso_hom_snd (n : SimplexCategoryᵒᵖ) :
    (cechBaseChangeStageIso cover f n).hom ≫
        pullback.snd ((Arrow.mk cover).augmentedCechNerve.hom.app n) f =
      (Arrow.mk (pullback.snd cover f)).augmentedCechNerve.hom.app n :=
  ((baseChangeCech_isPullback cover f).app n).isoPullback_hom_snd

/-- 概要：段の標準同型は全単体射に自然（論文 補題 3.2）。
方針：引き戻しの二射影で検査し、元の比較と増強の自然性に帰着する。
規約：段ごとの同型の存在だけには弱めない。
使われ方：実際の二つの Čech 図式の自然同型。 -/
theorem cechBaseChangeStageIso_naturality {i j : SimplexCategoryᵒᵖ} (α : i ⟶ j) :
    (Arrow.mk (pullback.snd cover f)).cechNerve.map α ≫
        (cechBaseChangeStageIso cover f j).hom =
      (cechBaseChangeStageIso cover f i).hom ≫
        (((cechOverDiagram cover ⋙ overBaseChange f) ⋙ Over.forget Y).map α) := by
  have hf : (((cechOverDiagram cover ⋙ overBaseChange f) ⋙ Over.forget Y).map α) ≫
      pullback.fst ((Arrow.mk cover).augmentedCechNerve.hom.app j) f =
      pullback.fst ((Arrow.mk cover).augmentedCechNerve.hom.app i) f ≫
        (Arrow.mk cover).cechNerve.map α :=
    pullback.lift_fst _ _ _
  have hs : (((cechOverDiagram cover ⋙ overBaseChange f) ⋙ Over.forget Y).map α) ≫
      pullback.snd ((Arrow.mk cover).augmentedCechNerve.hom.app j) f =
      pullback.snd ((Arrow.mk cover).augmentedCechNerve.hom.app i) f :=
    pullback.lift_snd _ _ _
  apply pullback.hom_ext
  · have hr : ((cechBaseChangeStageIso cover f i).hom ≫
          (((cechOverDiagram cover ⋙ overBaseChange f) ⋙ Over.forget Y).map α)) ≫
          pullback.fst ((Arrow.mk cover).augmentedCechNerve.hom.app j) f =
        (Arrow.mapCechNerve (baseChangeArrowToOriginal cover f)).app i ≫
          (Arrow.mk cover).cechNerve.map α :=
      (Category.assoc _ _ _).trans
        ((congrArg (_ ≫ ·) hf).trans
          ((Category.assoc _ _ _).symm.trans
            (congrArg (· ≫ _) (cechBaseChangeStageIso_hom_fst cover f i))))
    exact (Category.assoc _ _ _).trans
      ((congrArg (_ ≫ ·) (cechBaseChangeStageIso_hom_fst cover f j)).trans
        (((Arrow.mapCechNerve (baseChangeArrowToOriginal cover f)).naturality α).trans hr.symm))
  · have hr : ((cechBaseChangeStageIso cover f i).hom ≫
          (((cechOverDiagram cover ⋙ overBaseChange f) ⋙ Over.forget Y).map α)) ≫
          pullback.snd ((Arrow.mk cover).augmentedCechNerve.hom.app j) f =
        (Arrow.mk (pullback.snd cover f)).augmentedCechNerve.hom.app i :=
      (Category.assoc _ _ _).trans
        ((congrArg (_ ≫ ·) hs).trans (cechBaseChangeStageIso_hom_snd cover f i))
    exact (Category.assoc _ _ _).trans
      ((congrArg (_ ≫ ·) (cechBaseChangeStageIso_hom_snd cover f j)).trans
        ((((Arrow.mk (pullback.snd cover f)).augmentedCechNerve.hom.naturality α).trans
          (Category.comp_id _)).trans hr.symm))

/-- 概要：底変換 Čech と transfer 用の幾何図式の全体の自然同型（論文 補題 3.2）。
方針：二射影を保つ各段の同型と全単体射の自然性を組み合わせる。
規約：元の選択された引き戻しを変更しない。
使われ方：元の前層の像で実際の分裂 Čech 降下と比較する。 -/
noncomputable def cechBaseChangeGeometryIso :
    (Arrow.mk (pullback.snd cover f)).cechNerve ≅
      (cechOverDiagram cover ⋙ overBaseChange f) ⋙ Over.forget Y :=
  NatIso.ofComponents (cechBaseChangeStageIso cover f)
    (fun α ↦ cechBaseChangeStageIso_naturality cover f α)

/-- 概要：Over の底変換された増強は第二射影を保つ（論文 補題 3.2）。
方針：底変換関手の射は二射影による lift であることを使う。
規約：基底自身の底変換の標準同型を含む。
使われ方：前層の底変換された増強と実際の底変換 Čech 増強の一致。 -/
theorem cechBaseChangedToBase_snd (n : SimplexCategoryᵒᵖ) :
    ((overBaseChange f).map (overDiagramToBase (cechOverDiagram cover) n)).left ≫
        (overBaseChangeBaseIso f).hom.left =
      pullback.snd ((Arrow.mk cover).augmentedCechNerve.hom.app n) f :=
  pullback.lift_snd _ _ _

/-- 概要：段の標準同型は底変換された増強全体と可換（論文 補題 3.2）。
方針：増強先の標準同型で検査し、第二射影の二つの公式を使う。
規約：増強先を省略せず、元の Over 底変換の指定射を使う。
使われ方：反変前層を適用した増強比較の矢の圏の同型。 -/
theorem cechBaseChangeStageIso_augmentation (n : SimplexCategoryᵒᵖ) :
    (cechBaseChangeStageIso cover f n).hom ≫
        ((overBaseChange f).map (overDiagramToBase (cechOverDiagram cover) n)).left =
      (Arrow.mk (pullback.snd cover f)).augmentedCechNerve.hom.app n ≫
        (overBaseChangeBaseIso f).inv.left := by
  apply ((Over.forget Y).mapIso (overBaseChangeBaseIso f)).eq_comp_inv.mpr
  exact (Category.assoc _ _ _).trans
    ((congrArg (_ ≫ ·) (cechBaseChangedToBase_snd cover f n)).trans
      (cechBaseChangeStageIso_hom_snd cover f n))

variable {V : Type w} [Category.{t} V]

/-- 概要：元の前層の底変換 Čech 図式と実際の底変換被覆の像は自然同型（論文 補題 3.2）。
方針：幾何図式全体の自然同型を反対圏に移し、元の前層を適用する。
規約：同じ反変前層を全ての段と射で使う。
使われ方：transfer の比較先を実際の分裂 Čech 図式の像へ移す。 -/
noncomputable def cechBaseChangePresheafIso (F : Cᵒᵖ ⥤ V) :
    (cechOverDiagram cover).op ⋙ baseChangedPresheaf f F ≅
      (cechOverDiagram (pullback.snd cover f)).op ⋙ overPresheaf (Y := X) F :=
  Functor.isoWhiskerRight (NatIso.op (cechBaseChangeGeometryIso cover f)) F

/-- 概要：底変換された増強先の値と実際の基底の値の自然な同型（論文 補題 3.2）。
方針：基底自身の引き戻しの標準同型を元の前層で反変に写す。
規約：全ての単体次数に同じ基底の同型を使う。
使われ方：Čech 増強比較の矢の圏の同型の始域。 -/
noncomputable def cechBaseChangePresheafBaseIso (F : Cᵒᵖ ⥤ V) :
    (Functor.const (SimplexCategoryᵒᵖ)ᵒᵖ).obj
        ((baseChangedPresheaf f F).obj (op (Over.mk (𝟙 Y)))) ≅
      (Functor.const (SimplexCategoryᵒᵖ)ᵒᵖ).obj (F.obj (op X)) :=
  (Functor.const _).mapIso
    (F.mapIso (Iso.op (((Over.forget Y).mapIso (overBaseChangeBaseIso f)).symm)))

/-- 概要：transfer の底変換比較は実際の底変換被覆の増強比較と同型（論文 補題 3.2）。
方針：増強先と全図式の標準同型を組み合わせ、幾何的増強の可換性を反変に写す。
規約：矢の圏の同型であり、段ごとの値の同型に弱めない。
使われ方：実際の底変換被覆の分裂降下を transfer retract に渡す。 -/
noncomputable def cechBaseChangeAugmentationIso (F : Cᵒᵖ ⥤ V) :
    Arrow.mk (cechBaseChangedAugmentation cover f F) ≅
      Arrow.mk (cechPresheafAugmentation (pullback.snd cover f) F) :=
  Arrow.isoMk (cechBaseChangePresheafBaseIso f F)
    (cechBaseChangePresheafIso cover f F) (by
      ext n
      change F.map (overBaseChangeBaseIso f).inv.left.op ≫
          F.map ((Arrow.mk (pullback.snd cover f)).augmentedCechNerve.hom.app n.unop).op =
        F.map (((overBaseChange f).map
          (overDiagramToBase (cechOverDiagram cover) n.unop)).left).op ≫
          F.map (cechBaseChangeStageIso cover f n.unop).hom.op
      exact (F.map_comp (overBaseChangeBaseIso f).inv.left.op
        ((Arrow.mk (pullback.snd cover f)).augmentedCechNerve.hom.app n.unop).op).symm.trans
        ((congrArg F.map (congrArg Quiver.Hom.op
          (cechBaseChangeStageIso_augmentation cover f n.unop).symm)).trans
          (F.map_comp
            (((overBaseChange f).map
              (overDiagramToBase (cechOverDiagram cover) n.unop)).left).op
            (cechBaseChangeStageIso cover f n.unop).hom.op)))

variable [Preadditive V] [Linear ℚ V]

/-- 概要：元の Čech 比較は実際の底変換被覆の比較の retract（論文 補題 3.2）。
方針：transfer による retract と、増強を保つ底変換比較の自然同型を合成する。
規約：有限平坦 transfer の存在と局所 rank 公式は入力。被覆は指定された実際の引き戻し。
使われ方：底変換被覆の分裂降下を元の比較へ戻す。 -/
noncomputable def BaseChangeTransfer.cechBaseChangedCoverRetract
    {F : Cᵒᵖ ⥤ V} (tr : BaseChangeTransfer f F)
    (rank : ℕ) (positive : 0 < rank)
    (rank_identity : baseChangePresheafPullback f F ≫ tr.transfer =
      (rank : ℚ) • 𝟙 (overPresheaf (Y := Y) F)) :
    RetractArrow (cechPresheafAugmentation cover F)
      (cechPresheafAugmentation (pullback.snd cover f) F) :=
  (BaseChangeTransfer.cechAugmentationRetract cover tr rank positive rank_identity).trans
    (Retract.ofIso (cechBaseChangeAugmentationIso cover f F))

/-- 概要：実際の底変換被覆の全次数比較から元の比較へ戻す（論文 補題 3.2）。
方針：増強を含む実際の retract を図式関手で写し、全次数同型の retract 安定性を使う。
規約：図式関手・観測関手の実構成と分裂降下は別途供給する。
使われ方：L9 の Tot・π_* と接続する transfer 還元の終端。 -/
theorem BaseChangeTransfer.piCechComparison_of_baseChangedCover
    {D : Type*} [Category* D]
    (total : ((SimplexCategoryᵒᵖ)ᵒᵖ ⥤ V) ⥤ D)
    (observation : ℤ → D ⥤ ModuleCat ℚ)
    {F : Cᵒᵖ ⥤ V} (tr : BaseChangeTransfer f F)
    (rank : ℕ) (positive : 0 < rank)
    (rank_identity : baseChangePresheafPullback f F ≫ tr.transfer =
      (rank : ℚ) • 𝟙 (overPresheaf (Y := Y) F))
    (baseChanged : piIsomorphisms observation
      (total.map (cechPresheafAugmentation (pullback.snd cover f) F))) :
    piIsomorphisms observation (total.map (cechPresheafAugmentation cover F)) :=
  piIsomorphisms_of_retract observation
    ((BaseChangeTransfer.cechBaseChangedCoverRetract cover f tr rank positive rank_identity).map
      total) baseChanged

end SerrePositivity.KST.Descent
