module
public import SerrePositivity.KST.SConstruction.CoherentStrictPathEvaluation

/-! # 元の豊穣 Path 作用の定数性を外側面から回収する
概要：strict 図式の定数 Path 作用を、全射な面の Path 写像に沿って元の作用へ戻す。
方針：定数性を豊穣関手全体の命題として扱い、対象表示の変更と全射を通して移す。
規約：全単体次数を扱い、値の頂点は元の作用自身から取る。
使われ方：K prism の水平部分を元の段の写像の定数族へ照合する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SimplicialThickening SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 各高次 Path における値が Path 自身に依存しない、元の全豊穣作用の性質。 -/
def coherentPathActionsConstant {J : Type u} [LinearOrder J]
    {C : Type v} [Category.{u} C] [SimplicialCategory C]
    (R : EnrichedFunctor SSet.{u} (SimplicialThickening J) C) : Prop :=
  ∀ (a b : SimplicialThickening J) (d : ℕ) (P Q : (nerve (Path a.as b.as)) _⦋d⦌),
    (R.map a b).app (Opposite.op ⦋d⦌) P = (R.map a b).app (Opposite.op ⦋d⦌) Q

/-- 元の strict 図式の各豊穣単体は、全 Path 作用が定数である。 -/
lemma coherentStrictDiagramPathActionsConstant {I : Type u} [SmallCategory I]
    {C : Type v} [Category.{u} C] [SimplicialCategory C]
    (F : I ⥤ C) {n : ℕ} (s : (nerve I) _⦋n⦌) :
    coherentPathActionsConstant ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram F).app _ (ULift.up s)) := by
  intro a b d P Q
  rfl

/-- 全射による制限の各次数の定数性は、元の射の各次数の定数性を与える。 -/
lemma coherentPathValues_eq_of_epi {A B X : SSet.{u}} (i : A ⟶ B) [Epi i] (m : B ⟶ X)
    (hc : ∀ (d : ℕ) (P Q : A _⦋d⦌),
      (i ≫ m).app (Opposite.op ⦋d⦌) P = (i ≫ m).app (Opposite.op ⦋d⦌) Q)
    (d : ℕ) (P Q : B _⦋d⦌) :
    m.app (Opposite.op ⦋d⦌) P = m.app (Opposite.op ⦋d⦌) Q := by
  have hi : Function.Surjective (i.app (Opposite.op ⦋d⦌)) :=
    (epi_iff_surjective _).mp (by infer_instance)
  obtain ⟨p, rfl⟩ := hi P
  obtain ⟨q, rfl⟩ := hi Q
  exact hc d p q

/-- 全次数の値が入力に依存しなければ、元の指定頂点の定数族そのものである。 -/
lemma coherentPathMap_eq_const {A X : SSet.{u}} (m : A ⟶ X) (a : A _⦋0⦌)
    (hc : ∀ (d : ℕ) (P Q : A _⦋d⦌),
      m.app (Opposite.op ⦋d⦌) P = m.app (Opposite.op ⦋d⦌) Q) :
    m = SSet.const (m.app (Opposite.op ⦋0⦌) a) := by
  apply SSet.hom_ext
  rintro ⟨⟨d⟩⟩
  apply ConcreteCategory.hom_ext
  intro P
  have h := hc d P (A.map (SimplexCategory.const ⦋d⦌ ⦋0⦌ 0).op a)
  exact h.trans (NatTrans.naturality_apply m (SimplexCategory.const ⦋d⦌ ⦋0⦌ 0).op a)

end SerrePositivity.KST.SConstruction
