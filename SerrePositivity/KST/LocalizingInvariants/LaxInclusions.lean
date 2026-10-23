module

public import SerrePositivity.KST.LocalizingInvariants.LaxStableCategory
public import SerrePositivity.KST.LocalizingInvariants.ZeroArrowFamily
public import SerrePositivity.InfinityCategories.F2.CatInfinity.LaxPullbackLift

/-!
概要：元の lax pullback に、両因子からの実際の全単体上の包含関手を構成する。
方針：零値関手を端に持つ矢印の全族を、指定端点を保つ F2 の lift へ渡す。
規約：完全性・随伴・充満忠実性は別の工程。使われ方：Tamme Prop. 10 の両包含。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants.LaxInclusion

variable {C D E : StableCategory.{u}} (p : ExactMap C E) (q : ExactMap D E)

def zeroC : D.obj ⟶ C.obj := SSet.const (chosenZeroVertex C.obj).vertex
def zeroD : C.obj ⟶ D.obj := SSet.const (chosenZeroVertex D.obj).vertex

lemma zeroC_post (x : D.obj _⦋0⦌) :
    IsZeroVertex ((zeroC (D := D) ≫ p.hom).app (Opposite.op ⦋0⦌) x) := by
  change IsZeroVertex (p.hom.app _ ((zeroC (D := D)).app _ x))
  apply IsExactFunctor.preservesZero
  rw [zeroC, zeroDiagram_const_vertex]
  exact (chosenZeroVertex C.obj).isZero

lemma zeroD_post (x : C.obj _⦋0⦌) :
    IsZeroVertex ((zeroD (C := C) ≫ q.hom).app (Opposite.op ⦋0⦌) x) := by
  change IsZeroVertex (q.hom.app _ ((zeroD (C := C)).app _ x))
  apply IsExactFunctor.preservesZero
  rw [zeroD, zeroDiagram_const_vertex]
  exact (chosenZeroVertex D.obj).isZero

/-- d ↦ (0,d,0→q d) は全単体上で定義された実 ∞ 関手。 -/
def fromD : D.obj ⟶ (laxCategory p q).obj :=
  F2.laxPullbackLift p.hom q.hom zeroC (𝟙 D.obj)
    (ZeroArrowFamily.ofHomotopy (ZeroArrowFamily.fromZero _ q.hom (zeroC_post p)))
    (ZeroArrowFamily.ofHomotopy_source _) (by
      simpa only [Category.id_comp] using ZeroArrowFamily.ofHomotopy_target
        (ZeroArrowFamily.fromZero _ q.hom (zeroC_post p)))

/-- c ↦ (c,0,p c→0) は全単体上で定義された実 ∞ 関手。 -/
def fromC : C.obj ⟶ (laxCategory p q).obj :=
  F2.laxPullbackLift p.hom q.hom (𝟙 C.obj) zeroD
    (ZeroArrowFamily.ofHomotopy (ZeroArrowFamily.toZero p.hom _ (zeroD_post q)))
    (by
      simpa only [Category.id_comp] using ZeroArrowFamily.ofHomotopy_source
        (ZeroArrowFamily.toZero p.hom _ (zeroD_post q)))
    (ZeroArrowFamily.ofHomotopy_target _)

lemma fromD_fst : fromD p q ≫ (laxFst p q).hom = zeroC := F2.laxPullbackLift_fst ..
lemma fromD_snd : fromD p q ≫ (laxSnd p q).hom = 𝟙 D.obj := F2.laxPullbackLift_snd ..
lemma fromC_fst : fromC p q ≫ (laxFst p q).hom = 𝟙 C.obj := F2.laxPullbackLift_fst ..
lemma fromC_snd : fromC p q ≫ (laxSnd p q).hom = zeroD := F2.laxPullbackLift_snd ..

end SerrePositivity.KST.LocalizingInvariants.LaxInclusion
