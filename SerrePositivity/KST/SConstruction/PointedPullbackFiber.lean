module
public import SerrePositivity.KST.Spectra.PointedFiber
public import SerrePositivity.KST.Spectra.PullbackKanSequence

/-! # 点つき引き戻しの基点 fiber の比較
概要：引き戻した射の基点 fiber は元の射の基点 fiber と厳密に同型。
方針：二つの fiber の普遍性と引き戻しの普遍性で互いに逆の射を作る。
規約：Kan 性を仮定しない。使われ方：path を引き戻す homotopy fiber の loop 部分。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Limits
open Spectra

/-- 概要：引き戻した射の基点 fiber から元の基点 fiber への射。
方針：第一射影に沿う合成を元の fiber へ持ち上げる。
規約：点つき射の厳密な零合成を使う。使われ方：引き戻し fiber の同型の順方向。 -/
def pointedPullbackFiberTo {E A B : PointedSimplicialSet.{u}} (p : E ⟶ B) (g : A ⟶ B) :
    pointedFiber (pullback.snd p g) ⟶ pointedFiber p :=
  pointedFiberLiftOfZero p (pointedFiberι (pullback.snd p g) ≫ pullback.fst p g) (by
    rw [Category.assoc, pullback.condition, ← Category.assoc, pointedFiberι_comp, zero_comp])

/-- 概要：引き戻し fiber の比較は元の全空間への射と可換。
方針：fiber の持ち上げの回収式。
規約：厳密等号。使われ方：同型の互逆性と自然性。 -/
lemma pointedPullbackFiberTo_ι {E A B : PointedSimplicialSet.{u}} (p : E ⟶ B) (g : A ⟶ B) :
    pointedPullbackFiberTo p g ≫ pointedFiberι p =
      pointedFiberι (pullback.snd p g) ≫ pullback.fst p g := pointedFiberLiftOfZero_ι _ _ _

/-- 概要：元の基点 fiber から引き戻した射の基点 fiber への射。
方針：元の fiber の包含と零射を引き戻しへ貼り、第二射影の fiber へ持ち上げる。
規約：基点の保存は点つき普遍性で保持。使われ方：引き戻し fiber の同型の逆方向。 -/
def pointedPullbackFiberFrom {E A B : PointedSimplicialSet.{u}} (p : E ⟶ B) (g : A ⟶ B) :
    pointedFiber p ⟶ pointedFiber (pullback.snd p g) :=
  pointedFiberLiftOfZero (pullback.snd p g)
    (pullback.lift (pointedFiberι p) 0 (by simp)) (pullback.lift_snd ..)

/-- 概要：逆方向の比較を含めると二つの成分で指定した引き戻しの射となる。
方針：fiber の持ち上げの回収式。
規約：第二成分は厳密な零射。使われ方：逆方向の二つの射影の計算。 -/
lemma pointedPullbackFiberFrom_ι {E A B : PointedSimplicialSet.{u}} (p : E ⟶ B) (g : A ⟶ B) :
    pointedPullbackFiberFrom p g ≫ pointedFiberι (pullback.snd p g) =
      pullback.lift (pointedFiberι p) 0 (by simp) := pointedFiberLiftOfZero_ι _ _ _

/-- 概要：点つき引き戻しの基点 fiber は元の基点 fiber と同型。
方針：fiber の包含と二つの引き戻し射影で互逆性を検出する。
規約：底の写像 g についての同値性は要求しない。使われ方：loop の pullback fiber 表示。 -/
def pointedPullbackFiberIso {E A B : PointedSimplicialSet.{u}} (p : E ⟶ B) (g : A ⟶ B) :
    pointedFiber (pullback.snd p g) ≅ pointedFiber p where
  hom := pointedPullbackFiberTo p g
  inv := pointedPullbackFiberFrom p g
  hom_inv_id := by
    apply pointedFiber_hom_ext (pullback.snd p g)
    simp only [Category.assoc, pointedPullbackFiberFrom_ι, Category.id_comp]
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, pointedPullbackFiberTo_ι]
    · rw [Category.assoc, pullback.lift_snd, comp_zero, pointedFiberι_comp]
  inv_hom_id := by
    apply pointedFiber_hom_ext p
    rw [Category.assoc, pointedPullbackFiberTo_ι, ← Category.assoc,
      pointedPullbackFiberFrom_ι, pullback.lift_fst, Category.id_comp]

end SerrePositivity.KST.SConstruction
