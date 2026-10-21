module

public import SerrePositivity.InfinityCategories.F1.IntervalDiagramOverRestriction
public import SerrePositivity.InfinityCategories.Core.PrecompositionLifting

/-!
概要：整合する二つの両端固定区間 Hom の族を、底の pushout 上に貼る。
方針：元の展開した族を貼り、両端点を二つの制限で確認する。
規約：元の二図式と全パラメーターを保つ。
使われ方：分類先の区間 Hom の厳密な pushout 降下。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

variable {B X T : SSet.{u}} (F G : B ⟶ X) {a b c d : Over B}
  (f : a ⟶ b) (g : a ⟶ c) (i : b ⟶ d) (j : c ⟶ d)
  (hp : IsPushout f.left g.left i.left j.left)
  (s : T ⟶ intervalMappingSpace (functorVertex (c.hom ≫ F)) (functorVertex (c.hom ≫ G)))
  (t : T ⟶ intervalMappingSpace (functorVertex (b.hom ≫ F)) (functorVertex (b.hom ≫ G)))
  (hst : s ≫ intervalDiagramOverPre F G g = t ≫ intervalDiagramOverPre F G f)

/-- 同じ展開した二つの区間族を元の関手空間へ貼る。 -/
def intervalDiagramPushoutUncurry : (Δ[1] : SSet.{u}) ⊗ T ⟶ (ihom d.left).obj X :=
  (isPullback_pre_of_isPushout hp X).lift (intervalMappingUncurry s)
    (intervalMappingUncurry t) (by
      have h := congrArg intervalMappingUncurry hst
      simpa only [intervalDiagramOverPre_uncurry] using h)

/-- 展開した貼り合わせの最初の制限は元の区間族。 -/
lemma intervalDiagramPushoutUncurry_fst :
    intervalDiagramPushoutUncurry F G f g i j hp s t hst ≫ (pre j.left).app X =
      intervalMappingUncurry s := (isPullback_pre_of_isPushout hp X).lift_fst _ _ _

/-- 展開した貼り合わせの二番目の制限も元の区間族。 -/
lemma intervalDiagramPushoutUncurry_snd :
    intervalDiagramPushoutUncurry F G f g i j hp s t hst ≫ (pre i.left).app X =
      intervalMappingUncurry t := (isPullback_pre_of_isPushout hp X).lift_snd _ _ _

/-- 同じ貼り合わせの零端点は、指定した始域図式。 -/
lemma intervalDiagramPushoutUncurry_zero :
    prismEndpoint 0 T ≫ intervalDiagramPushoutUncurry F G f g i j hp s t hst =
      SSet.const (functorVertex (d.hom ≫ F)) := by
  apply (isPullback_pre_of_isPushout hp X).hom_ext
  · rw [Category.assoc, intervalDiagramPushoutUncurry_fst,
      intervalMappingUncurry_zero, SSet.const_comp]
    change SSet.const (functorVertex (c.hom ≫ F)) =
      SSet.const (functorVertex (j.left ≫ (d.hom ≫ F)))
    rw [← Category.assoc, j.w]
  · rw [Category.assoc, intervalDiagramPushoutUncurry_snd,
      intervalMappingUncurry_zero, SSet.const_comp]
    change SSet.const (functorVertex (b.hom ≫ F)) =
      SSet.const (functorVertex (i.left ≫ (d.hom ≫ F)))
    rw [← Category.assoc, i.w]

/-- 同じ貼り合わせの一端点は、指定した終域図式。 -/
lemma intervalDiagramPushoutUncurry_one :
    prismEndpoint 1 T ≫ intervalDiagramPushoutUncurry F G f g i j hp s t hst =
      SSet.const (functorVertex (d.hom ≫ G)) := by
  apply (isPullback_pre_of_isPushout hp X).hom_ext
  · rw [Category.assoc, intervalDiagramPushoutUncurry_fst,
      intervalMappingUncurry_one, SSet.const_comp]
    change SSet.const (functorVertex (c.hom ≫ G)) =
      SSet.const (functorVertex (j.left ≫ (d.hom ≫ G)))
    rw [← Category.assoc, j.w]
  · rw [Category.assoc, intervalDiagramPushoutUncurry_snd,
      intervalMappingUncurry_one, SSet.const_comp]
    change SSet.const (functorVertex (b.hom ≫ G)) =
      SSet.const (functorVertex (i.left ≫ (d.hom ≫ G)))
    rw [← Category.assoc, i.w]

end SerrePositivity.InfinityCategories
