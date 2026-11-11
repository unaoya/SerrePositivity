module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.SliceMap
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

/-!
概要：引き戻し内の固定図式からの全錐を、両成分の錐の引き戻しで表す。
方針：join からの射の普遍性を両成分に適用し、引き戻しの一意性で貼る。
規約：点ごとの写像空間だけでなく、任意の単体パラメーターを保持する。
使われ方：引き戻し内の反変 Hom の全自然比較と compact 性の証明。

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

variable {E D B K : SSet.{u}} (p : E ⟶ B) (q : D ⟶ B)
  (a : K ⟶ pullback p q)

/-- 概要：第二成分の錐を、第一成分と同じ標的図式の錐へ送る。
方針：元の引き戻しの可換条件で固定図式を合わせる。
規約：各錐の全 join 図式を保持する。
使われ方：錐圏の引き戻しの第二脚。 -/
def pullbackSliceBaseMap : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (a ≫ pullback.snd p q) ⟶
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver ((a ≫ pullback.fst p q) ≫ p) where
  app _ := ↾fun σ ↦ ⟨σ.val ≫ q, by
    rw [← Category.assoc, σ.property, Category.assoc, ← pullback.condition,
      ← Category.assoc]⟩
  naturality _ _ _ := by
    apply ConcreteCategory.hom_ext
    intro σ
    apply Subtype.ext
    exact Category.assoc _ _ _

/-- 概要：全錐の成分像は同じ底上で可換。
方針：各 join 図式への元の引き戻しの可換条件を使う。
規約：錐の射影を取り替えない。
使われ方：全錐の引き戻しへの標準比較。 -/
lemma pullbackSlice_condition :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverPostcomp a (pullback.fst p q) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverPostcomp (a ≫ pullback.fst p q) p =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverPostcomp a (pullback.snd p q) ≫ pullbackSliceBaseMap p q a := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro σ
  apply Subtype.ext
  change (σ.val ≫ pullback.fst p q) ≫ p = (σ.val ≫ pullback.snd p q) ≫ q
  simp only [Category.assoc, pullback.condition]

/-- 概要：元の全錐を両成分の全錐へ分解する標準比較。
方針：両後合成を可換条件で引き戻しへ合わせる。
規約：任意の固定図式を扱う。
使われ方：反変 Hom 全族の比較の全空間。 -/
def pullbackSliceComparison : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver a ⟶ pullback
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverPostcomp (a ≫ pullback.fst p q) p) (pullbackSliceBaseMap p q a) :=
  pullback.lift (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverPostcomp a (pullback.fst p q))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverPostcomp a (pullback.snd p q)) (pullbackSlice_condition p q a)

/-- 概要：可換な二つの成分錐の全単体を元の引き戻しへ貼る。
方針：各単体を join からの射と見て、元の引き戻しへ持ち上げる。
規約：固定図式 a 上の一致を厳密に保つ。
使われ方：全錐比較の逆写像の単体。 -/
def pullbackSliceLiftSimplex (n : SimplexCategoryᵒᵖ)
    (t : (pullback (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverPostcomp (a ≫ pullback.fst p q) p)
      (pullbackSliceBaseMap p q a)).obj n) : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver a).obj n := by
  let f := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverPostcomp (a ≫ pullback.fst p q) p
  let g := pullbackSliceBaseMap p q a
  let s := (pullback.fst f g).app n t
  let r := (pullback.snd f g).app n t
  have h : s.val ≫ p = r.val ≫ q := by
    exact congrArg Subtype.val
      (ConcreteCategory.congr_hom (NatTrans.congr_app (pullback.condition (f := f) (g := g)) n) t)
  refine ⟨pullback.lift s.val r.val h, ?_⟩
  apply pullback.hom_ext
  · rw [Category.assoc, pullback.lift_fst]
    exact s.property
  · rw [Category.assoc, pullback.lift_snd]
    exact r.property

/-- 概要：可換な両成分の全錐を元の全錐へ貼る。
方針：join 上の持ち上げの一意性で全単体作用との可換性を示す。
規約：任意の単体パラメーターで一つの射を構成する。
使われ方：錐圏の引き戻し比較の逆。 -/
def pullbackSliceComparisonInv : pullback
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverPostcomp (a ≫ pullback.fst p q) p) (pullbackSliceBaseMap p q a) ⟶
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver a where
  app n := ↾fun t ↦ pullbackSliceLiftSimplex p q a n t
  naturality {m n} α := by
    apply ConcreteCategory.hom_ext
    intro t
    apply Subtype.ext
    change (pullbackSliceLiftSimplex p q a n
      ((pullback (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverPostcomp (a ≫ pullback.fst p q) p)
        (pullbackSliceBaseMap p q a)).map α t)).val =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (stdSimplex.map α.unop) (𝟙 K) ≫
        (pullbackSliceLiftSimplex p q a m t).val
    dsimp only [pullbackSliceLiftSimplex]
    apply pullback.hom_ext
    · simp only [Category.assoc, pullback.lift_fst]
      exact congrArg Subtype.val
        (ConcreteCategory.congr_hom ((pullback.fst (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverPostcomp (a ≫ pullback.fst p q) p)
          (pullbackSliceBaseMap p q a)).naturality α) t)
    · simp only [Category.assoc, pullback.lift_snd]
      exact congrArg Subtype.val
        (ConcreteCategory.congr_hom ((pullback.snd (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverPostcomp (a ≫ pullback.fst p q) p)
          (pullbackSliceBaseMap p q a)).naturality α) t)


/-- 概要：引き戻し内の全錐圏は、元の両成分の全錐圏の引き戻しと同型。
方針：全 join 図式の分解と貼り合わせを、両射影の一意性で互いの逆とする。
規約：quasicategory 性や fibration 性を仮定しない。
使われ方：反変 Hom 全族の引き戻し比較。 -/
def pullbackSliceIso : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver a ≅ pullback
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverPostcomp (a ≫ pullback.fst p q) p) (pullbackSliceBaseMap p q a) where
  hom := pullbackSliceComparison p q a
  inv := pullbackSliceComparisonInv p q a
  hom_inv_id := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro σ
    apply Subtype.ext
    change (pullbackSliceLiftSimplex p q a n
      ((pullbackSliceComparison p q a).app n σ)).val = σ.val
    dsimp only [pullbackSliceLiftSimplex]
    apply pullback.hom_ext (f := p) (g := q)
    · rw [pullback.lift_fst]
      exact congrArg Subtype.val (ConcreteCategory.congr_hom
        (NatTrans.congr_app (pullback.lift_fst
          (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverPostcomp a (pullback.fst p q))
          (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverPostcomp a (pullback.snd p q))
          (pullbackSlice_condition p q a)) n) σ)
    · rw [pullback.lift_snd]
      exact congrArg Subtype.val (ConcreteCategory.congr_hom
        (NatTrans.congr_app (pullback.lift_snd
          (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverPostcomp a (pullback.fst p q))
          (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverPostcomp a (pullback.snd p q))
          (pullbackSlice_condition p q a)) n) σ)
  inv_hom_id := by
    apply pullback.hom_ext
    · simp only [Category.assoc, pullbackSliceComparison, pullback.lift_fst,
        Category.id_comp]
      apply SSet.hom_ext
      intro n
      apply ConcreteCategory.hom_ext
      intro t
      apply Subtype.ext
      exact pullback.lift_fst _ _ _
    · simp only [Category.assoc, pullbackSliceComparison, pullback.lift_snd,
        Category.id_comp]
      apply SSet.hom_ext
      intro n
      apply ConcreteCategory.hom_ext
      intro t
      apply Subtype.ext
      exact pullback.lift_snd _ _ _

/-- 概要：錐圏の比較同型の第一脚は元の第一射影への後合成。
方針：引き戻しの持ち上げの第一脚を計算する。
規約：元の全図式 a を固定する。
使われ方：分類された全反変 Hom の第一成分の同定。 -/
lemma pullbackSliceIso_hom_fst :
    (pullbackSliceIso p q a).hom ≫ pullback.fst _ _ =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverPostcomp a (pullback.fst p q) :=
  pullback.lift_fst _ _ _

/-- 概要：錐圏の比較同型の第二脚は元の第二射影への後合成。
方針：引き戻しの持ち上げの第二脚を計算する。
規約：元の全図式 a を固定する。
使われ方：分類された全反変 Hom の第二成分の同定。 -/
lemma pullbackSliceIso_hom_snd :
    (pullbackSliceIso p q a).hom ≫ pullback.snd _ _ =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverPostcomp a (pullback.snd p q) :=
  pullback.lift_snd _ _ _

/-- 概要：全錐比較の第一脚は元の頂点の第一成分を保つ。
方針：join の左因子上の制限と後合成を交換する。
規約：全次数で元の錐射影を保つ。
使われ方：底の引き戻し上の比較としての利用。 -/
lemma pullbackSliceIso_projection_fst :
    (pullbackSliceIso p q a).hom ≫ pullback.fst _ _ ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (a ≫ pullback.fst p q) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection a ≫ pullback.fst p q := by
  rw [← Category.assoc, pullbackSliceIso_hom_fst]
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro σ
  change yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (stdSimplex.obj n.unop) K ≫ (σ.val ≫ pullback.fst p q)) =
    (pullback.fst p q).app n (yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (stdSimplex.obj n.unop) K ≫ σ.val))
  rw [← Category.assoc, yonedaEquiv_comp]

/-- 概要：全錐比較の第二脚は元の頂点の第二成分を保つ。
方針：join の左因子上の制限と後合成を交換する。
規約：全次数で元の錐射影を保つ。
使われ方：底の引き戻し上の比較としての利用。 -/
lemma pullbackSliceIso_projection_snd :
    (pullbackSliceIso p q a).hom ≫ pullback.snd _ _ ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (a ≫ pullback.snd p q) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection a ≫ pullback.snd p q := by
  rw [← Category.assoc, pullbackSliceIso_hom_snd]
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro σ
  change yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (stdSimplex.obj n.unop) K ≫ (σ.val ≫ pullback.snd p q)) =
    (pullback.snd p q).app n (yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (stdSimplex.obj n.unop) K ≫ σ.val))
  rw [← Category.assoc, yonedaEquiv_comp]

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
