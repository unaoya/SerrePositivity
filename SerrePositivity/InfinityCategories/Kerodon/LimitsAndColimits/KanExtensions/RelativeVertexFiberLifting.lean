module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.VertexFiberMap
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

/-!
概要：可換四角形の引き戻しへの比較の全境界充填を頂点 fiber の比較へ制限する。
方針：標的 fiber の持ち上げ問題を、始域の底を定値とする引き戻し上の問題へ移す。
規約：二つの底は異なってよい。
使われ方：相対 coslice の端点比較から固定終点の写像空間の制限を得る。

対応節は Kerodon 7.3（Tag 02Y1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions

/-- 概要：可換四角形は底の頂点とその像の fiber の間の射を誘導する。
方針：始域の fiber を全空間へ含め、四角形の可換性で標的の fiber へ持ち上げる。
規約：二つの底の射 u は任意。
使われ方：固定終点の coslice の後合成の一般形。 -/
def kanRelativeVertexFiberMap {E F B C : SSet.{u}}
    (p : E ⟶ B) (q : F ⟶ C) (f : E ⟶ F) (u : B ⟶ C)
    (h : p ≫ u = f ≫ q) (b : B _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p b ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber q (u.app (Opposite.op ⦋0⦌) b) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift q _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p b ≫ f) (by
    rw [Category.assoc, ← h, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι_comp, SSet.const_comp])

/-- 概要：fiber の誘導射を全空間へ含めると元の射への合成となる。
方針：fiber への持ち上げの包含の式を使う。
規約：四角形の可換性の証明の選択は問わない。
使われ方：頂点 fiber への全境界充填の移送。 -/
lemma kanRelativeVertexFiberMap_ι {E F B C : SSet.{u}}
    (p : E ⟶ B) (q : F ⟶ C) (f : E ⟶ F) (u : B ⟶ C)
    (h : p ≫ u = f ≫ q) (b : B _⦋0⦌) :
    kanRelativeVertexFiberMap p q f u h b ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι q (u.app (Opposite.op ⦋0⦌) b) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p b ≫ f := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift_ι _ _ _ _

/-- 概要：引き戻しへの比較の持ち上げ性は対応する頂点 fiber の比較へ移る。
方針：始域の底を定値とする持ち上げを作り、その延長を同じ fiber へ戻す。
規約：左の射と四つの単体集合は任意。
使われ方：相対余錐制限の内ホーン充填を図式固定の余錐の族へ移す。 -/
lemma kanRelativeVertexFiberMap_hasLiftingProperty {E F B C A T : SSet.{u}}
    (p : E ⟶ B) (q : F ⟶ C) (f : E ⟶ F) (u : B ⟶ C)
    (h : p ≫ u = f ≫ q) (i : A ⟶ T) [HasLiftingProperty i (pullback.lift p f h)]
    (b : B _⦋0⦌) : HasLiftingProperty i (kanRelativeVertexFiberMap p q f u h b) := by
  constructor
  intro a d sq
  let t := pullback.lift (f := u) (g := q) (SSet.const b : T ⟶ B)
    (d ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι q (u.app (Opposite.op ⦋0⦌) b)) (by
      rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι_comp, SSet.comp_const, SSet.const_comp])
  have sq' : CommSq (a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p b) i (pullback.lift p f h) t := by
    constructor
    apply pullback.hom_ext
    · simp only [t, Category.assoc, pullback.lift_fst, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι_comp, SSet.comp_const]
    · simp only [t, Category.assoc, pullback.lift_snd]
      have hs := congrArg (fun z ↦ z ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι q (u.app (Opposite.op ⦋0⦌) b)) sq.w
      simp only [Category.assoc, kanRelativeVertexFiberMap_ι] at hs
      exact hs
  have hlp : sq'.lift ≫ p = SSet.const b := by
    have hs := congrArg (fun z ↦ z ≫ pullback.fst u q) sq'.fac_right
    simpa only [t, Category.assoc, pullback.lift_fst] using hs
  have hlf : sq'.lift ≫ f = d ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι q (u.app (Opposite.op ⦋0⦌) b) := by
    have hs := congrArg (fun z ↦ z ≫ pullback.snd u q) sq'.fac_right
    simpa only [t, Category.assoc, pullback.lift_snd] using hs
  refine CommSq.HasLift.mk' {
    l := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift p b sq'.lift hlp
    fac_left := ?_
    fac_right := ?_ }
  · apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_hom_ext p b
    rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift_ι]
    exact sq'.fac_left
  · apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_hom_ext q (u.app (Opposite.op ⦋0⦌) b)
    rw [Category.assoc, kanRelativeVertexFiberMap_ι, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift_ι]
    exact hlf

/-- 概要：引き戻しへの比較が inner fibration なら各頂点 fiber の比較もそうである。
方針：任意の inner anodyne な射の持ち上げ性を fiber へ制限する。
規約：二つの底は異なってよい。
使われ方：図式固定の余錐の族の後合成の inner fibration 性。 -/
instance kanRelativeVertexFiberMap_innerFibration {E F B C : SSet.{u}}
    (p : E ⟶ B) (q : F ⟶ C) (f : E ⟶ F) (u : B ⟶ C)
    (h : p ≫ u = f ≫ q) [InnerFibration (pullback.lift p f h)] (b : B _⦋0⦌) :
    InnerFibration (kanRelativeVertexFiberMap p q f u h b) where
  mem := by
    intro A T i hi
    have := InnerFibration.mem (q := pullback.lift p f h) i hi
    exact kanRelativeVertexFiberMap_hasLiftingProperty p q f u h i b

/-- 概要：引き戻しへの比較が自明 Kan fibration なら各頂点の fiber の比較もそうである。
方針：始域の底を定値とする引き戻しへの持ち上げ問題を充填し、同じ fiber に戻す。
規約：四つの単体集合は任意で充填性を別途要求しない。
使われ方：相対始点境界充填から固定終点の写像空間の比較を得る。 -/
lemma kanRelativeVertexFiberMap_trivialKanFibration {E F B C : SSet.{u}}
    (p : E ⟶ B) (q : F ⟶ C) (f : E ⟶ F) (u : B ⟶ C)
    (h : p ≫ u = f ≫ q) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (pullback.lift p f h)] (b : B _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (kanRelativeVertexFiberMap p q f u h b) where
  mem := by
    intro A D i hi
    have := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration.mem (p := pullback.lift p f h) i hi
    constructor
    intro a d sq
    let t := pullback.lift (f := u) (g := q) (SSet.const b : D ⟶ B)
      (d ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι q (u.app (Opposite.op ⦋0⦌) b)) (by
        rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι_comp, SSet.comp_const, SSet.const_comp])
    have sq' : CommSq (a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p b) i (pullback.lift p f h) t := by
      constructor
      apply pullback.hom_ext
      · simp only [t, Category.assoc, pullback.lift_fst, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι_comp, SSet.comp_const]
      · simp only [t, Category.assoc, pullback.lift_snd]
        have hs := congrArg (fun z ↦ z ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι q (u.app (Opposite.op ⦋0⦌) b)) sq.w
        simp only [Category.assoc, kanRelativeVertexFiberMap_ι] at hs
        exact hs
    have hlp : sq'.lift ≫ p = SSet.const b := by
      have hs := congrArg (fun z ↦ z ≫ pullback.fst u q) sq'.fac_right
      simpa only [t, Category.assoc, pullback.lift_fst] using hs
    have hlf : sq'.lift ≫ f = d ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι q (u.app (Opposite.op ⦋0⦌) b) := by
      have hs := congrArg (fun z ↦ z ≫ pullback.snd u q) sq'.fac_right
      simpa only [t, Category.assoc, pullback.lift_snd] using hs
    refine CommSq.HasLift.mk' {
      l := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift p b sq'.lift hlp
      fac_left := ?_
      fac_right := ?_ }
    · apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_hom_ext p b
      rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift_ι]
      exact sq'.fac_left
    · apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_hom_ext q (u.app (Opposite.op ⦋0⦌) b)
      rw [Category.assoc, kanRelativeVertexFiberMap_ι, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift_ι]
      exact hlf

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions
