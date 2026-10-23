module

public import SerrePositivity.InfinityCategories.F1.FunctorCategories.RelativeFunctorOverPrecomposition
public import SerrePositivity.InfinityCategories.F1.MappingSpaces.IntervalDiagramRestriction
public import SerrePositivity.InfinityCategories.Core.PrecompositionLifting

/-!
概要：元の相対関手の整合する二つの族を、始域の pushout 上へ厳密に貼る。
方針：通常の関手空間の pullback で貼り、底の固定条件を両制限で検証する。
規約：元の相対 Hom と全パラメーターを保持する。
使われ方：共有頂点を持つ区間の Hom の貼り合わせ。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories

variable {E B T : SSet.{u}} (q : E ⟶ B) {a b c d : Over B}
variable (f : a ⟶ b) (g : a ⟶ c) (i : b ⟶ d) (j : c ⟶ d)
variable (hp : IsPushout f.left g.left i.left j.left)
variable (s : T ⟶ relativeFunctorSpace q c.hom) (t : T ⟶ relativeFunctorSpace q b.hom)
variable (hst : s ≫ relativeFunctorOverPre q g = t ≫ relativeFunctorOverPre q f)

/-- 元の相対 Hom の二つの族を、同じ通常の関手空間へ貼った族。 -/
def relativeFunctorPushoutUnrestrictedLift : T ⟶ (ihom d.left).obj E :=
  (isPullback_pre_of_isPushout hp E).lift (s ≫ vertexFiberι _ _)
    (t ≫ vertexFiberι _ _) (by
    calc
      (s ≫ vertexFiberι _ _) ≫ (pre g.left).app E =
          (s ≫ relativeFunctorOverPre q g) ≫ vertexFiberι _ _ := by
        simp only [Category.assoc, relativeFunctorOverPre_ι]
      _ = (t ≫ relativeFunctorOverPre q f) ≫ vertexFiberι _ _ := by rw [hst]
      _ = _ := by simp only [Category.assoc, relativeFunctorOverPre_ι])

/-- 同じ貼り合わせの最初の制限は元の族。 -/
lemma relativeFunctorPushoutUnrestrictedLift_fst :
    relativeFunctorPushoutUnrestrictedLift q f g i j hp s t hst ≫ (pre j.left).app E =
      s ≫ vertexFiberι ((ihom c.left).map q) (functorVertex c.hom) :=
  (isPullback_pre_of_isPushout hp E).lift_fst _ _ _

/-- 同じ貼り合わせの二番目の制限も元の族。 -/
lemma relativeFunctorPushoutUnrestrictedLift_snd :
    relativeFunctorPushoutUnrestrictedLift q f g i j hp s t hst ≫ (pre i.left).app E =
      t ≫ vertexFiberι ((ihom b.left).map q) (functorVertex b.hom) :=
  (isPullback_pre_of_isPushout hp E).lift_snd _ _ _

/-- 同じ通常の関手の貼り合わせは、元の固定された底の図式を保持する。 -/
lemma relativeFunctorPushoutUnrestrictedLift_projection :
    relativeFunctorPushoutUnrestrictedLift q f g i j hp s t hst ≫
        (ihom d.left).map q =
      SSet.const (functorVertex d.hom) := by
  apply (isPullback_pre_of_isPushout hp B).hom_ext
  · rw [Category.assoc, (pre j.left).naturality q, ← Category.assoc,
      relativeFunctorPushoutUnrestrictedLift_fst, Category.assoc, vertexFiberι_comp,
      SSet.const_comp,
      functorVertex_precomposition, j.w, SSet.comp_const]
  · rw [Category.assoc, (pre i.left).naturality q, ← Category.assoc,
      relativeFunctorPushoutUnrestrictedLift_snd, Category.assoc, vertexFiberι_comp,
      SSet.const_comp,
      functorVertex_precomposition, i.w, SSet.comp_const]

/-- 元の整合する相対 Hom の二つの族を、同じ pushout 上の相対 Hom の族へ貼る。 -/
def relativeFunctorPushoutLift : T ⟶ relativeFunctorSpace q d.hom :=
  vertexFiberLift _ _ (relativeFunctorPushoutUnrestrictedLift q f g i j hp s t hst)
    (relativeFunctorPushoutUnrestrictedLift_projection q f g i j hp s t hst)

/-- 相対 Hom への貼り合わせを含めると、同じ通常の関手の貼り合わせになる。 -/
lemma relativeFunctorPushoutLift_ι :
    relativeFunctorPushoutLift q f g i j hp s t hst ≫
      vertexFiberι ((ihom d.left).map q) (functorVertex d.hom) =
        relativeFunctorPushoutUnrestrictedLift q f g i j hp s t hst :=
  vertexFiberLift_ι _ _ _ _

end SerrePositivity.InfinityCategories
