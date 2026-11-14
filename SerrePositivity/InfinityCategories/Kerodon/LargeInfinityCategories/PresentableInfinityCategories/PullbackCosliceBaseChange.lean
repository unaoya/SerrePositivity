module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PullbackCosliceComparison
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.CosliceEndpointFibration
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IntervalCosliceSource
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
概要：引き戻し内の全余錐圏を、同じ底へ戻した成分の余錐圏と比較する。
方針：成分の射影を元の引き戻しへ底変換し、全余錐比較の普遍性で貼る。
規約：元の引き戻しの全頂点を底として保持する。
使われ方：引き戻しの共変 Hom 全族への分類・保存判定の適用。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

variable {E D B K : SSet.{u}} (p : E ⟶ B) (q : D ⟶ B) (a : K ⟶ pullback p q)

/-- 概要：第二成分から共通の余錐圏への射は元の可変頂点を保つ。
方針：全 join 図式の右因子への制限と後合成を交換する。
規約：全次数での射の等式。
使われ方：成分の余錐を元の底上へ戻す。 -/
lemma pullbackCosliceBaseMap_projection :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.pullbackCosliceBaseMap p q a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection ((a ≫ pullback.fst p q) ≫ p) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (a ≫ pullback.snd p q) ≫ q := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro σ
  change yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr K (stdSimplex.obj n.unop) ≫ (σ.val ≫ q)) =
    q.app n (yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr K (stdSimplex.obj n.unop) ≫ σ.val))
  rw [← Category.assoc, yonedaEquiv_comp]

/-- 概要：第一成分の余錐圏を元の引き戻し全体へ戻した全空間。
方針：余錐の可変頂点の射影を元の第一射影で底変換する。
規約：固定図式 a を保持する。
使われ方：第一成分の共変 Hom の全族。 -/
def pullbackCosliceLeft :=
  pullback (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (a ≫ pullback.fst p q)) (pullback.fst p q)

/-- 概要：第二成分の余錐圏を元の引き戻し全体へ戻した全空間。
方針：余錐の可変頂点の射影を元の第二射影で底変換する。
規約：固定図式 a を保持する。
使われ方：第二成分の共変 Hom の全族。 -/
def pullbackCosliceRight :=
  pullback (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (a ≫ pullback.snd p q)) (pullback.snd p q)

/-- 概要：共通標的の余錐圏を元の引き戻し全体へ戻した全空間。
方針：元の共通標的への射で可変頂点の射影を底変換する。
規約：底への射は第一射影による合成に固定する。
使われ方：共通標的の共変 Hom の全族。 -/
def pullbackCosliceBase :=
  pullback (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection ((a ≫ pullback.fst p q) ≫ p)) (pullback.fst p q ≫ p)

/-- 概要：第一成分の余錐の後合成を同じ元の底上で行う。
方針：元の後合成と底変換の第二射影を合わせる。
規約：底の全パラメーターを変えない。
使われ方：共変 Hom の cospan の第一脚。 -/
def pullbackCosliceLeftMap : pullbackCosliceLeft p q a ⟶ pullbackCosliceBase p q a :=
  pullback.lift
    (pullback.fst _ _ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderPostcomp (a ≫ pullback.fst p q) p)
    (pullback.snd _ _) (by
      rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.sliceUnderPostcomp_projection, ← Category.assoc,
        pullback.condition, Category.assoc])

/-- 概要：第二成分の余錐の後合成を同じ元の底上で行う。
方針：元の後合成と引き戻しの可換条件を合わせる。
規約：共通標的の固定図式を第一成分と一致させる。
使われ方：共変 Hom の cospan の第二脚。 -/
def pullbackCosliceRightMap : pullbackCosliceRight p q a ⟶ pullbackCosliceBase p q a :=
  pullback.lift
    (pullback.fst _ _ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.pullbackCosliceBaseMap p q a)
    (pullback.snd _ _) (by
      rw [Category.assoc, pullbackCosliceBaseMap_projection, ← Category.assoc,
        pullback.condition, Category.assoc, pullback.condition])

/-- 概要：元の全余錐は底を保つ第一成分の余錐を定める。
方針：第一射影への後合成と元の可変頂点を合わせる。
規約：元の底の頂点を厳密に固定する。
使われ方：底変換された全余錐の引き戻し錐の第一脚。 -/
def pullbackCosliceToLeft : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder a ⟶ pullbackCosliceLeft p q a :=
  pullback.lift (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderPostcomp a (pullback.fst p q)) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection a)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.sliceUnderPostcomp_projection a (pullback.fst p q))

/-- 概要：元の全余錐は底を保つ第二成分の余錐を定める。
方針：第二射影への後合成と元の可変頂点を合わせる。
規約：元の底の頂点を厳密に固定する。
使われ方：底変換された全余錐の引き戻し錐の第二脚。 -/
def pullbackCosliceToRight : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder a ⟶ pullbackCosliceRight p q a :=
  pullback.lift (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderPostcomp a (pullback.snd p q)) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection a)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.sliceUnderPostcomp_projection a (pullback.snd p q))

/-- 概要：底変換された両成分の全余錐は共通標的上で一致する。
方針：全余錐比較の可換条件と元の可変頂点を使う。
規約：底上の射の厳密な等式。
使われ方：元の coslice を頂点とする指定引き戻し錐。 -/
lemma pullbackCosliceBaseChange_condition :
    pullbackCosliceToLeft p q a ≫ pullbackCosliceLeftMap p q a =
      pullbackCosliceToRight p q a ≫ pullbackCosliceRightMap p q a := by
  apply pullback.hom_ext
  · simp only [Category.assoc, pullbackCosliceLeftMap, pullbackCosliceRightMap,
      pullbackCosliceToLeft, pullbackCosliceToRight, pullback.lift_fst,
      pullback.lift_fst_assoc]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.pullbackCoslice_condition p q a
  · simp only [Category.assoc, pullbackCosliceLeftMap, pullbackCosliceRightMap,
      pullback.lift_snd, pullbackCosliceToLeft, pullbackCosliceToRight]

/-- 概要：全余錐比較の元の正方形は引き戻し。
方針：構成した全単体の同型と両脚の厳密な回収を使う。
規約：同型な対象へ置き換えず元の全余錐を頂点にする。
使われ方：同じ底へ戻した全族の普遍射の構成。 -/
lemma pullbackCoslice_isPullback : IsPullback
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderPostcomp a (pullback.fst p q)) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderPostcomp a (pullback.snd p q))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderPostcomp (a ≫ pullback.fst p q) p) (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.pullbackCosliceBaseMap p q a) :=
  IsPullback.of_iso_pullback ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.pullbackCoslice_condition p q a⟩ (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.pullbackCosliceIso p q a)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.pullbackCosliceIso_hom_fst p q a) (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.pullbackCosliceIso_hom_snd p q a)

/-- 概要：底変換された可換な二つの余錐の可変頂点は一致する。
方針：共通標的への等式を元の底への第二射影で評価する。
規約：全パラメーターの射の等式を保持する。
使われ方：元の coslice へ貼った族の底への射影を判定する。 -/
lemma pullbackCosliceBaseChange_base_eq {T : SSet.{u}}
    (f : T ⟶ pullbackCosliceLeft p q a) (g : T ⟶ pullbackCosliceRight p q a)
    (h : f ≫ pullbackCosliceLeftMap p q a = g ≫ pullbackCosliceRightMap p q a) :
    f ≫ pullback.snd _ _ = g ≫ pullback.snd _ _ := by
  have h' := congrArg (fun r : T ⟶ pullbackCosliceBase p q a ↦
    r ≫ pullback.snd (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection ((a ≫ pullback.fst p q) ≫ p))
      (pullback.fst p q ≫ p)) h
  simpa only [Category.assoc, pullbackCosliceLeftMap, pullbackCosliceRightMap,
    pullback.lift_snd] using h'

/-- 概要：底変換された可換な全二族を元の全余錐へ貼る。
方針：元の余錐圏の引き戻しの普遍射を使う。
規約：元の固定図式 a を保つ。
使われ方：底変換された全余錐の引き戻し錐の普遍射。 -/
def pullbackCosliceBaseChangeLift {T : SSet.{u}}
    (f : T ⟶ pullbackCosliceLeft p q a) (g : T ⟶ pullbackCosliceRight p q a)
    (h : f ≫ pullbackCosliceLeftMap p q a = g ≫ pullbackCosliceRightMap p q a) :
    T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder a :=
  (pullbackCoslice_isPullback p q a).lift (f ≫ pullback.fst _ _) (g ≫ pullback.fst _ _) (by
    have h' := congrArg (fun r : T ⟶ pullbackCosliceBase p q a ↦
      r ≫ pullback.fst (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection ((a ≫ pullback.fst p q) ≫ p))
        (pullback.fst p q ≫ p)) h
    simpa only [Category.assoc, pullbackCosliceLeftMap, pullbackCosliceRightMap,
      pullback.lift_fst] using h')

/-- 概要：貼った全余錐の可変頂点は元の二族の共通頂点。
方針：元の引き戻しの両射影で余錐の射影を判定する。
規約：可変頂点の同型でなく厳密な等式。
使われ方：底変換された全族の普遍射の両脚の回収。 -/
lemma pullbackCosliceBaseChangeLift_projection {T : SSet.{u}}
    (f : T ⟶ pullbackCosliceLeft p q a) (g : T ⟶ pullbackCosliceRight p q a)
    (h : f ≫ pullbackCosliceLeftMap p q a = g ≫ pullbackCosliceRightMap p q a) :
    pullbackCosliceBaseChangeLift p q a f g h ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection a =
      f ≫ pullback.snd _ _ := by
  apply pullback.hom_ext (f := p) (g := q)
  · calc
      _ = (pullbackCosliceBaseChangeLift p q a f g h ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderPostcomp a (pullback.fst p q)) ≫
            _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (a ≫ pullback.fst p q) := by
              simp only [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.sliceUnderPostcomp_projection]
      _ = (f ≫ pullback.fst _ _) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (a ≫ pullback.fst p q) := by
        rw [pullbackCosliceBaseChangeLift, IsPullback.lift_fst]
      _ = _ := by rw [Category.assoc, pullback.condition, Category.assoc]
  · rw [pullbackCosliceBaseChange_base_eq p q a f g h]
    calc
      _ = (pullbackCosliceBaseChangeLift p q a f g h ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderPostcomp a (pullback.snd p q)) ≫
            _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (a ≫ pullback.snd p q) := by
              simp only [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.sliceUnderPostcomp_projection]
      _ = (g ≫ pullback.fst _ _) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (a ≫ pullback.snd p q) := by
        rw [pullbackCosliceBaseChangeLift, IsPullback.lift_snd]
      _ = _ := by rw [Category.assoc, pullback.condition, Category.assoc]

/-- 概要：貼った全余錐の第一脚は元の第一族。
方針：成分の余錐と共通頂点の両射影を回収する。
規約：元の底上の射としての等式。
使われ方：全余錐の引き戻し錐の普遍性。 -/
lemma pullbackCosliceBaseChangeLift_left {T : SSet.{u}}
    (f : T ⟶ pullbackCosliceLeft p q a) (g : T ⟶ pullbackCosliceRight p q a)
    (h : f ≫ pullbackCosliceLeftMap p q a = g ≫ pullbackCosliceRightMap p q a) :
    pullbackCosliceBaseChangeLift p q a f g h ≫ pullbackCosliceToLeft p q a = f := by
  apply pullback.hom_ext
  · simp only [Category.assoc, pullbackCosliceToLeft, pullback.lift_fst]
    exact (pullbackCoslice_isPullback p q a).lift_fst _ _ _
  · simp only [Category.assoc, pullbackCosliceToLeft, pullback.lift_snd]
    exact pullbackCosliceBaseChangeLift_projection p q a f g h

/-- 概要：貼った全余錐の第二脚は元の第二族。
方針：成分の余錐と二族の共通頂点を回収する。
規約：元の底上の射としての等式。
使われ方：全余錐の引き戻し錐の普遍性。 -/
lemma pullbackCosliceBaseChangeLift_right {T : SSet.{u}}
    (f : T ⟶ pullbackCosliceLeft p q a) (g : T ⟶ pullbackCosliceRight p q a)
    (h : f ≫ pullbackCosliceLeftMap p q a = g ≫ pullbackCosliceRightMap p q a) :
    pullbackCosliceBaseChangeLift p q a f g h ≫ pullbackCosliceToRight p q a = g := by
  apply pullback.hom_ext
  · simp only [Category.assoc, pullbackCosliceToRight, pullback.lift_fst]
    exact (pullbackCoslice_isPullback p q a).lift_snd _ _ _
  · simp only [Category.assoc, pullbackCosliceToRight, pullback.lift_snd]
    exact (pullbackCosliceBaseChangeLift_projection p q a f g h).trans
      (pullbackCosliceBaseChange_base_eq p q a f g h)

/-- 概要：元の coslice は同じ底へ戻した成分の余錐圏の引き戻し。
方針：任意のパラメーターの可換な二族を貼り、一意性を元の全余錐比較へ戻す。
規約：元の固定図式と可変頂点を全て保持する。
使われ方：同じ底上の left fibrations の全引き戻し判定。 -/
lemma pullbackCosliceBaseChange_isPullback : IsPullback
    (pullbackCosliceToLeft p q a) (pullbackCosliceToRight p q a)
    (pullbackCosliceLeftMap p q a) (pullbackCosliceRightMap p q a) := by
  apply IsPullback.of_isLimit (c := PullbackCone.mk
    (pullbackCosliceToLeft p q a) (pullbackCosliceToRight p q a)
    (pullbackCosliceBaseChange_condition p q a))
  refine PullbackCone.IsLimit.mk _
    (fun s ↦ pullbackCosliceBaseChangeLift p q a s.fst s.snd s.condition)
    (fun s ↦ pullbackCosliceBaseChangeLift_left p q a s.fst s.snd s.condition)
    (fun s ↦ pullbackCosliceBaseChangeLift_right p q a s.fst s.snd s.condition) ?_
  intro s m hm₁ hm₂
  apply (pullbackCoslice_isPullback p q a).hom_ext
  · have hh := congrArg (fun r : s.pt ⟶ pullbackCosliceLeft p q a ↦ r ≫ pullback.fst _ _)
      (hm₁.trans (pullbackCosliceBaseChangeLift_left p q a s.fst s.snd s.condition).symm)
    simpa only [Category.assoc, pullbackCosliceToLeft, pullback.lift_fst] using hh
  · have hh := congrArg (fun r : s.pt ⟶ pullbackCosliceRight p q a ↦ r ≫ pullback.fst _ _)
      (hm₂.trans (pullbackCosliceBaseChangeLift_right p q a s.fst s.snd s.condition).symm)
    simpa only [Category.assoc, pullbackCosliceToRight, pullback.lift_fst] using hh

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HTT "5.4.5.4" (partial := special) "仮定：元の平方を一方が categorical fibration である strict pullback 模型で与える（Lean が強い：任意の別の homotopy Cartesian 平方を入力しない）。結論：元の全余スライス平方は strict pullback で、その同じ脚は categorical lifting を保つため対応する Cat∞ の錐も極限（この模型で一致）。"] _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.pullbackCoslice_isPullback
