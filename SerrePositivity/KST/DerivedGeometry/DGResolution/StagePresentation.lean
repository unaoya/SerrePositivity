module

public import SerrePositivity.KST.DerivedGeometry.DGResolution.CellEmbedding
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Colim

/-!
# 半自由分解の具体的な段階表示

概要：添加列の生成元・微分・増大像と、各有限段階から極限への単射性・網羅性を示す。
方針：既存の具体的生成元添加、次数別分裂、完全な filtered colimit を使う。
規約：分解の存在や半自由性を未証明フィールドとして受け取らない。
使われ方：Drinfeld §13.4・Lemma 13.5、KST D4 の dg 分解。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v

namespace SerrePositivity.KST.DerivedGeometry.DGResolution

open CategoryTheory Limits HomologicalComplex
open SerrePositivity.DifferentialGraded

variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/--
概要：第 n 段階へ添加する、閉元と指定原始元の組の添字型。
方針：前段階の増大関手に対する全境界 cell を取る。
規約：次数は任意の整数、両端の対象も任意。
使われ方：Drinfeld Lemma 13.5 の生成元の列。
-/
abbrev StageGeneratorIndex (n : ℕ) := (DGCategoryCellResolution.stage A D n).CellIndex

/--
概要：指定された境界を埋める、次段階の具体的な生成元。
方針：有限語の直和の一生成元成分に球の単位元を入れる。
規約：閉元とは限らない。
使われ方：Drinfeld §13.4・Lemma 13.5 の半自由な生成元添加。
-/
def stageGenerator (n : ℕ) (i : StageGeneratorIndex A D n) :
    (DGCategoryCellResolution.stageHom A D (n + 1) i.1 i.2.1).X i.2.2.degree :=
  @DGCellAttachment.Family.generatorElement A _ D
    (DGCategoryCellResolution.stage A D n).category _
    (DGCategoryCellResolution.stage A D n).cells inferInstance i

/--
概要：次段階の生成元の微分は前段階の指定閉元の像。
方針：一生成元の有限語に対する追加微分の計算を使う。
規約：生成元の微分は前段階に属する。
使われ方：Drinfeld §13.4・Lemma 13.5 の半自由条件。
-/
theorem stageGenerator_differential (n : ℕ) (i : StageGeneratorIndex A D n) :
    (DGCategoryCellResolution.stageHom A D (n + 1) i.1 i.2.1).d
      i.2.2.degree (i.2.2.degree + 1) (stageGenerator A D n i) =
      (DGCategoryCellResolution.transition A D n i.1 i.2.1).f (i.2.2.degree + 1)
        i.2.2.cycle.val :=
  @DGCellAttachment.Family.differential_generatorElement A _ D
    (DGCategoryCellResolution.stage A D n).category _
    (DGCategoryCellResolution.stage A D n).cells inferInstance i

/--
概要：生成元の増大像は指定された標的の原始元。
方針：生成元への具体的な評価関手の計算を使う。
規約：原始元を後から選び直さない。
使われ方：Drinfeld Lemma 13.5 の全射準同型と境界充填。
-/
theorem stageGenerator_augmentation (n : ℕ) (i : StageGeneratorIndex A D n) :
    (DGCategoryCellResolution.stageAugmentation A D (n + 1) i.1 i.2.1).f i.2.2.degree
      (stageGenerator A D n i) = i.2.2.primitive :=
  @DGCellAttachment.Family.PrimitiveData.attachedEvaluation_generator A _ D
    (DGCategoryCellResolution.stage A D n).category _ inferInstance
    (DGCategoryCellResolution.stage A D n).cells D inferInstance
    (DGCategoryCellResolution.stage A D n).toDGFunctor
    (DGCategoryCellResolution.stage A D n).cellPrimitives i

/--
概要：添加列の各遷移は次数ごとに分裂単射。
方針：対応する生成元添加の空語射影を使う。
規約：追加微分後の複体の分裂は要求しない。
使われ方：Drinfeld Lemma 13.5 の増大列。
-/
instance transition_degree_splitMono (n : ℕ) (x y : D) (q : ℤ) :
    IsSplitMono ((DGCategoryCellResolution.transition A D n x y).f q) :=
  @attachment_degree_splitMono A _ D (DGCategoryCellResolution.stage A D n).category
    _ inferInstance (DGCategoryCellResolution.stage A D n).cells x y q

/--
概要：添加列の各遷移は複体の圏で単射。
方針：各次数の分裂単射から得る。
規約：元の dg 圏の Hom の平坦性は不要。
使われ方：Drinfeld Lemma 13.5 の段階フィルトレーション。
-/
instance transition_mono (n : ℕ) (x y : D) :
    Mono (DGCategoryCellResolution.transition A D n x y) :=
  HomologicalComplex.mono_of_mono_f _ fun _ => inferInstance

/--
概要：添加列の任意の二段階間の遷移は単射。
方針：隣接遷移の合成について帰納する。
規約：添字間の射は自然数の順序の射。
使われ方：Drinfeld Lemma 13.5 の余極限への包含。
-/
instance homDiagram_map_mono (x y : D) (m n : ℕ) (f : m ⟶ n) :
    Mono ((DGCategoryCellResolution.homDiagram A D x y).map f) := by
  have h : ∀ n (h : m ≤ n),
      Mono ((DGCategoryCellResolution.homDiagram A D x y).map (homOfLE h)) := by
    intro n h
    induction n, h using Nat.le_induction with
    | base =>
        change Mono ((DGCategoryCellResolution.homDiagram A D x y).map (𝟙 m))
        infer_instance
    | succ n hn ih =>
        let := ih
        have he : homOfLE (hn.trans (Nat.le_succ n)) =
            homOfLE hn ≫ homOfLE (Nat.le_succ n) := Subsingleton.elim _ _
        rw [he, CategoryTheory.Functor.map_comp]
        have : Mono ((DGCategoryCellResolution.homDiagram A D x y).map
            (homOfLE (Nat.le_succ n))) := by
          change Mono ((Functor.ofSequence fun k =>
            DGCategoryCellResolution.transition A D k x y).map _)
          rw [Functor.ofSequence_map_homOfLE_succ]
          infer_instance
        infer_instance
  exact h n (leOfHom f)

/--
概要：各有限段階は極限の Hom 複体へ次数ごとに単射で入る。
方針：評価後の filtered colimit と加群圏の AB5 を使う。
規約：分裂することは主張しない。
使われ方：Drinfeld Lemma 13.5 の半自由な増大列の合併。
-/
instance stageInclusion_degree_mono (k : ℕ) (x y : D) (q : ℤ) :
    Mono ((DGCategoryCellResolution.stageInclusion A D k x y).f q) := by
  have : AB5OfSize.{0, 0} (ModuleCat.{u} A) := AB5OfSize_of_univLE (ModuleCat.{u} A)
  let ev := HomologicalComplex.eval (ModuleCat.{u} A) (ComplexShape.up ℤ) q
  let F := DGCategoryCellResolution.homDiagram A D x y ⋙ ev
  have : ∀ (i j : ℕ) (f : i ⟶ j), Mono (F.map f) := by
    intro i j f
    dsimp [F, ev]
    infer_instance
  exact (isColimitOfPreserves ev
    (colimit.isColimit (DGCategoryCellResolution.homDiagram A D x y))).mono_ι_app_of_isFiltered k

/--
概要：各有限段階は極限の Hom 複体へ単射で入る。
方針：次数ごとの単射性をまとめる。
規約：極限への包含の単射性を追加仮定にしない。
使われ方：Drinfeld Lemma 13.5 の段階表示。
-/
instance stageInclusion_mono (k : ℕ) (x y : D) :
    Mono (DGCategoryCellResolution.stageInclusion A D k x y) :=
  HomologicalComplex.mono_of_mono_f _ fun _ => inferInstance

/--
概要：分解の Hom の任意の斉次元は有限段階の元から来る。
方針：次数評価が保つ具体的 filtered colimit の元の表示を使う。
規約：斉次元の次数や段階の一様な有界性は要求しない。
使われ方：Drinfeld Lemma 13.5 の段階列の網羅性。
-/
theorem homogeneous_finiteStage (x y : Objects A D) (q : ℤ)
    (a : (homObject A (Objects A D) x y).X q) :
    ∃ (k : ℕ) (b : (DGCategoryCellResolution.stageHom A D k x.val y.val).X q),
      (DGCategoryCellResolution.stageInclusion A D k x.val y.val).f q b = a := by
  let : PreservesFilteredColimitsOfSize.{0, 0} (forget (ModuleCat.{u} A)) :=
    preservesSmallestFilteredColimits_of_preservesFilteredColimits _
  let ev := HomologicalComplex.eval (ModuleCat.{u} A) (ComplexShape.up ℤ) q
  exact Concrete.isColimit_exists_rep
    (DGCategoryCellResolution.homDiagram A D x.val y.val ⋙ ev)
    (isColimitOfPreserves ev (colimit.isColimit _)) a

/--
概要：分解の Hom の閉元は有限段階の閉元から来る。
方針：具体的な逐次余極限の閉元の有限段表示を使う。
規約：単なる斉次元の表示と閉元の表示を区別する。
使われ方：Drinfeld Lemma 13.5 の極限での準同型性。
-/
theorem cycle_finiteStage (x y : Objects A D) (q : ℤ)
    (a : complexCycles A (homObject A (Objects A D) x y) q) :
    ∃ (k : ℕ) (b : complexCycles A
        (DGCategoryCellResolution.stageHom A D k x.val y.val) q),
      (DGCategoryCellResolution.stageInclusion A D k x.val y.val).f q b.val = a.val :=
  complexSequentialColimit_cycle_rep A (DGCategoryCellResolution.homDiagram A D x.val y.val)
    (colimit.cocone _) (colimit.isColimit _) q a

/--
概要：有限段階で添加した指定生成元の極限内の像。
方針：次段階の生成元を余極限の包含で送る。
規約：両端の対象ラベルは変えない。
使われ方：Drinfeld §13.4・Lemma 13.5 の極限の生成元。
-/
def limitGenerator (n : ℕ) (i : StageGeneratorIndex A D n) :
    (DGCategoryCellResolution.candidateHom A D i.1 i.2.1).X i.2.2.degree :=
  (DGCategoryCellResolution.stageInclusion A D (n + 1) i.1 i.2.1).f i.2.2.degree
    (stageGenerator A D n i)

/--
概要：極限の指定生成元の微分は前段階の指定閉元の像。
方針：包含の chain map 条件と遷移射の余極限への整合性を使う。
規約：極限の微分も有限段階の指定微分を維持する。
使われ方：Drinfeld §13.4・Lemma 13.5 の半自由分解。
-/
theorem limitGenerator_differential (n : ℕ) (i : StageGeneratorIndex A D n) :
    (DGCategoryCellResolution.candidateHom A D i.1 i.2.1).d
      i.2.2.degree (i.2.2.degree + 1) (limitGenerator A D n i) =
      (DGCategoryCellResolution.stageInclusion A D n i.1 i.2.1).f (i.2.2.degree + 1)
        i.2.2.cycle.val := by
  have h := congrArg (fun f => f (stageGenerator A D n i))
    ((DGCategoryCellResolution.stageInclusion A D (n + 1) i.1 i.2.1).comm
      i.2.2.degree (i.2.2.degree + 1))
  change (DGCategoryCellResolution.candidateHom A D i.1 i.2.1).d _ _
      (limitGenerator A D n i) =
    (DGCategoryCellResolution.stageInclusion A D (n + 1) i.1 i.2.1).f _
      ((DGCategoryCellResolution.stageHom A D (n + 1) i.1 i.2.1).d _ _
        (stageGenerator A D n i)) at h
  rw [stageGenerator_differential] at h
  exact h.trans (congrArg (fun f => f.f (i.2.2.degree + 1) i.2.2.cycle.val)
    (DGCategoryCellResolution.transition_inclusion A D n i.1 i.2.1))

/--
概要：極限の指定生成元の増大像は指定原始元。
方針：各段階の増大関手と極限の増大関手の可換性を使う。
規約：極限へ移っても原始元を変えない。
使われ方：Drinfeld Lemma 13.5 の全射準同型。
-/
theorem limitGenerator_augmentation (n : ℕ) (i : StageGeneratorIndex A D n) :
    (DGCategoryCellResolution.candidateAugmentation A D i.1 i.2.1).f i.2.2.degree
      (limitGenerator A D n i) = i.2.2.primitive := by
  have h := congrArg (fun f => f.f i.2.2.degree (stageGenerator A D n i))
    (DGCategoryCellResolution.stageInclusion_augmentation A D (n + 1) i.1 i.2.1)
  exact h.trans (stageGenerator_augmentation A D n i)

end SerrePositivity.KST.DerivedGeometry.DGResolution
