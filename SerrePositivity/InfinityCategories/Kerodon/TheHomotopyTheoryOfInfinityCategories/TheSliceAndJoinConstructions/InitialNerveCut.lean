module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.StrictCones

/-!
概要：WithInitial の nerve の射列を、新しい始対象の区間と元の圏の区間に分ける切断。
方針：始対象を零、元の対象を一に送る順序写像の先頭区間の逆像に Join.pullCut を使う。
規約：切断は新しい始対象の頂点数であり、零と全頂点数も許す。
使われ方：HTT 1.2.8、Kerodon 4.3.5（Tag 017V）、7.5.3.12（Tag 03B1） の nerve と点の join の同定。

対応節は Kerodon 4.3（Tag 015M）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
variable {C D : Type u} [SmallCategory C] [SmallCategory D]

/-- 概要：WithInitial の新しい始対象と元の対象を二点の順序集合で区別する。
方針：新しい始対象を零、元の対象を一に送る。
規約：元の圏の対象の等号判定は使わない。
使われ方：HTT 1.2.8、Kerodon 4.3.5（Tag 017V）、7.5.3.12（Tag 03B1） の nerve と join の比較。 -/
def initialNerveTag : WithInitial C → Fin 2
  | .star => 0
  | .of _ => 1
/-- 概要：WithInitial の射は新しい始対象か元の対象かを表す値を増加させる。
方針：元の対象から新しい始対象への射がないことを使う。
規約：どちらの値も Fin 2 の元として扱う。
使われ方：HTT 1.2.8、Kerodon 4.3.5（Tag 017V）、7.5.3.12（Tag 03B1） の nerve と join の比較。 -/
lemma initialNerveTag_le {x y : WithInitial C} (f : x ⟶ y) :
    initialNerveTag x ≤ initialNerveTag y := by
  cases x <;> cases y
  · exact le_rfl
  · exact PEmpty.elim f
  · change (0 : Fin 2) ≤ 1
    decide
  · exact le_rfl
/-- 概要：WithInitial の射列は始対象か元の対象かを表す単調写像を定める。
方針：射列の各射にタグの単調性を適用する。
規約：射列の頂点数は n+1。
使われ方：HTT 1.2.8、Kerodon 4.3.5（Tag 017V）、7.5.3.12（Tag 03B1） の nerve と join の比較。 -/
def initialNerveChainTag {n : ℕ} (F : ComposableArrows (WithInitial C) n) :
    Fin (n + 1) →o Fin 2 where
  toFun i := initialNerveTag (F.obj i)
  monotone' _ _ h := initialNerveTag_le (F.map (homOfLE h))
/-- 概要：WithInitial の射列の新しい始対象の初区間の頂点数。
方針：二点への単調写像の零への先頭区間の逆像を取る。
規約：値は自然数で、零と n+1 を含む。
使われ方：HTT 1.2.8、Kerodon 4.3.5（Tag 017V）、7.5.3.12（Tag 03B1） の nerve と join の比較。 -/
def initialNerveCut {n : ℕ} (F : ComposableArrows (WithInitial C) n) : ℕ :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.pullCut (initialNerveChainTag F) 1
/-- 概要：新しい始対象の区間の頂点数は射列の全頂点数以下。
方針：先頭区間の逆像の頂点数の上界を使う。
規約：全ての頂点が新しい始対象の場合も含む。
使われ方：HTT 1.2.8、Kerodon 4.3.5（Tag 017V）、7.5.3.12（Tag 03B1） の nerve と join の比較。 -/
lemma initialNerveCut_le {n : ℕ} (F : ComposableArrows (WithInitial C) n) :
    initialNerveCut F ≤ n + 1 := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.pullCut_le _ _
/-- 概要：切断より前の頂点であることと新しい始対象であることは同値。
方針：Join.pullCut の先頭区間の特徴づけを二点へのタグに適用する。
規約：元の対象の同型ではなく新しい始対象との等式で特徴づける。
使われ方：HTT 1.2.8、Kerodon 4.3.5（Tag 017V）、7.5.3.12（Tag 03B1） の nerve と join の比較。 -/
lemma initialNerve_lt_cut_iff {n : ℕ} (F : ComposableArrows (WithInitial C) n)
    (i : Fin (n + 1)) : i.val < initialNerveCut F ↔ F.obj i = WithInitial.star := by
  rw [initialNerveCut, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.lt_pullCut_iff]
  change (initialNerveTag (F.obj i)).val < 1 ↔ _
  cases F.obj i <;> simp [initialNerveTag]
/-- 概要：射列の制限による切断の変化は join の切断の引き戻しに一致する。
方針：二点への単調写像の合成と先頭区間の逆像の合成則を使う。
規約：面と退化を含む全ての単体作用素に可換。
使われ方：HTT 1.2.8、Kerodon 4.3.5（Tag 017V）、7.5.3.12（Tag 03B1） の nerve と join の比較。 -/
lemma initialNerveCut_precomp {m n : ℕ} (α : ⦋m⦌ ⟶ ⦋n⦌)
    (F : (nerve (WithInitial C)) _⦋n⦌) :
    initialNerveCut ((nerve (WithInitial C)).map α.op F) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.pullCut α.toOrderHom (initialNerveCut F) := by
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.pullCut ((initialNerveChainTag F).comp α.toOrderHom) 1 = _
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.pullCut_comp _ _ _
/-- 概要：元の圏の関手の WithInitial への拡張は切断を保つ。
方針：新しい始対象と元の対象の両方のタグが保存されることを確認する。
規約：F の忠実性や対象上の単射性は要求しない。
使われ方：HTT 1.2.8、Kerodon 4.3.5（Tag 017V）、7.5.3.12（Tag 03B1） の nerve と join の比較。 -/
lemma initialNerveCut_map (G : C ⥤ D) {n : ℕ} (F : ComposableArrows (WithInitial C) n) :
    initialNerveCut (((WithInitial.map G).mapComposableArrows n).obj F) =
      initialNerveCut F := by
  unfold initialNerveCut
  congr 1
  ext i
  change (initialNerveTag ((WithInitial.map G).obj (F.obj i))).val =
    (initialNerveTag (F.obj i)).val
  cases F.obj i <;> rfl

/-- 概要：元の圏から包含した射列の切断は零。
方針：全ての頂点が元の対象であることを切断の特徴づけに使う。
規約：元の圏の射列の長さは任意。
使われ方：HTT 1.2.8、Kerodon 4.3.5（Tag 017V） の join の両端の同定。 -/
lemma initialNerveCut_incl {n : ℕ} (F : ComposableArrows C n) :
    initialNerveCut ((WithInitial.incl.mapComposableArrows n).obj F) = 0 := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.cut_ext (initialNerveCut_le _) (Nat.zero_le (n + 1))
  intro i
  rw [initialNerve_lt_cut_iff]
  change WithInitial.of (F.obj i) = WithInitial.star ↔ i.val < 0
  simp
/-- 概要：新しい始対象で一定の射列の切断は全頂点数。
方針：全ての頂点が新しい始対象であることと切断の一意性を使う。
規約：零次元の一点の射列も含む。
使われ方：HTT 1.2.8、Kerodon 4.3.5（Tag 017V） の join の両端の同定。 -/
lemma initialNerveCut_constStar (n : ℕ) :
    initialNerveCut ((Functor.const (Fin (n + 1))).obj (WithInitial.star : WithInitial C)) =
      n + 1 := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.cut_ext (initialNerveCut_le _) (le_refl (n + 1))
  intro i
  rw [initialNerve_lt_cut_iff]
  change WithInitial.star = (WithInitial.star : WithInitial C) ↔ i.val < n + 1
  simp [i.isLt]

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
