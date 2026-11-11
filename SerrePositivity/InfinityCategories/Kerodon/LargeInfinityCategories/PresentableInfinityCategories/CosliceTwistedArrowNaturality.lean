module

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.Source
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.HomComparison

/-!
概要：元の coslice と始点固定 twisted arrow の比較は関手の後合成と可換。
方針：実全空間の射を pullback の普遍性で構成し、二つの射影を比較する。
規約：quasicategory 性を要求せず、元の比較射の厳密な等式を使う。
使われ方：P-12 の指定 Yoneda 単位の始点固定評価と元の共変 Hom 比較の照合。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

/-- 概要：元の coslice の twisted arrow 比較は全空間の後合成と可換。
方針：各単体で同じ崩壊写像の後に元の関手を合成する。
規約：任意の固定点の射を許す。使われ方：始点固定比較の第一射影の計算。 -/
lemma cosliceTwistedArrowMap_postcomp {A C : SSet.{u}} (F : A ⟶ C)
    (p : (Δ[0] : SSet.{u}) ⟶ A) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.cosliceTwistedArrowMap p ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSubdivisionMap F =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderPostcomp p F ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.cosliceTwistedArrowMap (p ≫ F) := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro s
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.cosliceEdgewiseCollapse n.unop ≫ s.val) ≫ F =
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.cosliceEdgewiseCollapse n.unop ≫ (s.val ≫ F)
  exact Category.assoc _ _ _

/-- 概要：始点固定の底への包含は、元の関手の両変数への作用と可換。
方針：各単体で定値の第一成分と可変な第二成分を比較する。
規約：固定点は元の F による像を取る。使われ方：始点固定全空間写像の構成。 -/
lemma twistedArrowSourceInclusion_postcomp {A C : SSet.{u}} (F : A ⟶ C) (a : A _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowSourceInclusion a ≫ (SSet.opFunctor.map F ⊗ₘ F) =
      F ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowSourceInclusion (F.app (Opposite.op ⦋0⦌) a) := by
  apply CartesianMonoidalCategory.hom_ext
  · simp only [Category.assoc, tensorHom_fst, _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowSourceInclusion,
      lift_fst_assoc, lift_fst, SSet.const_comp, SSet.comp_const]
    rfl
  · simp only [Category.assoc, tensorHom_snd, _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowSourceInclusion,
      lift_snd_assoc, lift_snd, Category.id_comp, Category.comp_id]

/-- 概要：始点固定 twisted arrow の元の全空間を F で後合成する。
方針：元の twisted arrow 写像と射影の自然性を pullback へ持ち上げる。
規約：底の写像は F。使われ方：共同 Hom 比較の始点固定の実模型。 -/
def twistedArrowSourcePostcomp {A C : SSet.{u}} (F : A ⟶ C) (a : A _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowSource a ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowSource (F.app (Opposite.op ⦋0⦌) a) :=
  pullback.lift
    (pullback.fst (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowProjection A) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowSourceInclusion a) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSubdivisionMap F)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowSourceProjection a ≫ F) (by
      rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowProjection_naturality, ← Category.assoc,
        pullback.condition, Category.assoc, twistedArrowSourceInclusion_postcomp]
      rfl)

/-- 概要：始点固定全空間の後合成は底の元の F を保つ。
方針：pullback の第二射影則を使う。
規約：全空間の厳密な等式。使われ方：分類の実正方形への入力。 -/
lemma twistedArrowSourcePostcomp_projection {A C : SSet.{u}} (F : A ⟶ C) (a : A _⦋0⦌) :
    twistedArrowSourcePostcomp F a ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowSourceProjection (F.app (Opposite.op ⦋0⦌) a) =
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowSourceProjection a ≫ F := pullback.lift_snd _ _ _

/-- 概要：始点固定全空間の後合成の第一射影は元の twisted arrow 写像。
方針：pullback の第一射影則を使う。
規約：元の全空間射を保持する。使われ方：coslice 比較の後合成との照合。 -/
lemma twistedArrowSourcePostcomp_fst {A C : SSet.{u}} (F : A ⟶ C) (a : A _⦋0⦌) :
    twistedArrowSourcePostcomp F a ≫
      pullback.fst (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowProjection C)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowSourceInclusion (F.app (Opposite.op ⦋0⦌) a)) =
      pullback.fst (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowProjection A) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowSourceInclusion a) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSubdivisionMap F := pullback.lift_fst _ _ _

/-- 概要：点の表示の等式による coslice の移送は元の射影を保つ。
方針：点の等式を消去する。
規約：固定点の表示のみを移す。使われ方：元の比較射を再利用した点の射による表示。 -/
lemma sliceUnderProjection_eqToHom {A : SSet.{u}}
    {p q : (Δ[0] : SSet.{u}) ⟶ A} (h : p = q) :
    eqToHom (congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder h) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection q = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection p := by
  cases h
  exact Category.id_comp _

/-- 概要：点の表示の等式による coslice の移送は元の twisted arrow 比較を保つ。
方針：点の等式を消去する。
規約：元の比較射を保持する。使われ方：点の射で指定した比較の第一射影。 -/
lemma cosliceTwistedArrowMap_eqToHom {A : SSet.{u}}
    {p q : (Δ[0] : SSet.{u}) ⟶ A} (h : p = q) :
    eqToHom (congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder h) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.cosliceTwistedArrowMap q = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.cosliceTwistedArrowMap p := by
  cases h
  exact Category.id_comp _

/-- 概要：固定点を点からの射で指定した、元の始点固定 twisted arrow 比較。
方針：点と頂点の全単射の逆則で始域を移送し、既存の同じ比較を使う。
規約：既存の比較を選び直さない。
使われ方：後合成後の固定点を保持した実正方形の記述。 -/
def pointCosliceToTwistedArrowSource {A : SSet.{u}} (p : (Δ[0] : SSet.{u}) ⟶ A) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder p ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowSource (SSet.yonedaEquiv p) :=
  eqToHom (congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder
    (Equiv.symm_apply_apply (SSet.yonedaEquiv (X := A) (n := ⦋0⦌)) p).symm) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.cosliceToTwistedArrowSource (SSet.yonedaEquiv p)

/-- 概要：点の射で指定した比較は元の coslice 射影を保つ。
方針：既存の第二射影則と点の表示の移送則を使う。
規約：固定点は元の p。使われ方：後合成正方形の第二射影の照合。 -/
lemma pointCosliceToTwistedArrowSource_projection {A : SSet.{u}}
    (p : (Δ[0] : SSet.{u}) ⟶ A) :
    pointCosliceToTwistedArrowSource p ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowSourceProjection (SSet.yonedaEquiv p) = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection p := by
  rw [pointCosliceToTwistedArrowSource, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.cosliceToTwistedArrowSource_projection]
  exact sliceUnderProjection_eqToHom
    (Equiv.symm_apply_apply (SSet.yonedaEquiv (X := A) (n := ⦋0⦌)) p).symm

/-- 概要：点の射で指定した比較の第一射影は元の twisted arrow 比較。
方針：既存の第一射影則と点の表示の移送則を使う。
規約：元の比較写像を保持する。使われ方：後合成正方形の第一射影の照合。 -/
lemma pointCosliceToTwistedArrowSource_fst {A : SSet.{u}}
    (p : (Δ[0] : SSet.{u}) ⟶ A) :
    pointCosliceToTwistedArrowSource p ≫
      pullback.fst (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowProjection A) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowSourceInclusion (SSet.yonedaEquiv p)) =
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.cosliceTwistedArrowMap p := by
  rw [pointCosliceToTwistedArrowSource, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.cosliceToTwistedArrowSource_fst]
  exact cosliceTwistedArrowMap_eqToHom
    (Equiv.symm_apply_apply (SSet.yonedaEquiv (X := A) (n := ⦋0⦌)) p).symm

/-- 概要：元の coslice 比較と始点固定 twisted arrow の後合成は厳密に可換。
方針：pullback の両射影で検出し、元の twisted arrow 比較の後合成則を使う。
規約：全空間射の等式であり、点ごとの同値へ弱めない。
使われ方：指定 Yoneda 単位と指定共変 Hom 比較の分類正方形の入力。 -/
lemma pointCosliceToTwistedArrowSource_postcomp {A C : SSet.{u}} (F : A ⟶ C)
    (p : (Δ[0] : SSet.{u}) ⟶ A) :
    pointCosliceToTwistedArrowSource p ≫ twistedArrowSourcePostcomp F (SSet.yonedaEquiv p) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderPostcomp p F ≫ pointCosliceToTwistedArrowSource (p ≫ F) := by
  apply pullback.hom_ext
  · rw [Category.assoc, twistedArrowSourcePostcomp_fst, ← Category.assoc,
      pointCosliceToTwistedArrowSource_fst, cosliceTwistedArrowMap_postcomp, Category.assoc]
    exact (congrArg
      (fun m : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (p ≫ F) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.TwistedArrow C ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderPostcomp p F ≫ m)
      (pointCosliceToTwistedArrowSource_fst (p ≫ F))).symm
  · change (pointCosliceToTwistedArrowSource p ≫
        twistedArrowSourcePostcomp F (SSet.yonedaEquiv p)) ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowSourceProjection (F.app (Opposite.op ⦋0⦌) (SSet.yonedaEquiv p)) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderPostcomp p F ≫ pointCosliceToTwistedArrowSource (p ≫ F)) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowSourceProjection (SSet.yonedaEquiv (p ≫ F))
    rw [Category.assoc, twistedArrowSourcePostcomp_projection, ← Category.assoc,
      pointCosliceToTwistedArrowSource_projection, ← _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.sliceUnderPostcomp_projection p F]
    exact (congrArg
      (fun m : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (p ≫ F) ⟶ C ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderPostcomp p F ≫ m)
      (pointCosliceToTwistedArrowSource_projection (p ≫ F))).symm.trans
        (Category.assoc _ _ _).symm

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
