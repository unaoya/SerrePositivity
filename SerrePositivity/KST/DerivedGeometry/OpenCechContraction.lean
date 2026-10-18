module

public import SerrePositivity.KST.DerivedGeometry.SplitOpenCech
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Cech
public import Mathlib.Algebra.Homology.Opposite
public import Mathlib.Algebra.Homology.SingleHomology
public import Mathlib.Algebra.Homology.QuasiIso

/-!
概要：全体を含む開被覆の実際の Čech 複体の正次数の完全性。
方針：先頭挿入の追加退化を評価し、対圏の交代境界複体の収縮を移す。
規約：Mathlib の cechComplexFunctor と同じ複体を比較する。
使われ方：TT §3、Toën §3.2 のアフィン局所化後の Čech 計算。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v a b
open CategoryTheory Limits
namespace SerrePositivity.KST.DerivedGeometry
variable {X : Type u} [TopologicalSpace X] {ι : Type v} (U : ι → TopologicalSpace.Opens X)
  {A : Type a} [Category.{b} A] [Abelian A] [HasProducts.{v} A]
  (P : (TopologicalSpace.Opens X)ᵒᵖ ⥤ A)

/--
概要：形式的な開被覆の増大 Čech 対象を前層で対圏へ評価する。
方針：形式的余積を切断の積に送る既存評価関手を使う。
規約：前層の加法性や層条件は要求しない。
使われ方：TT §3、Toën §3.2 の Čech 収縮の入力。
-/
def openCechEvaluation : SimplicialObject.Augmented Aᵒᵖ :=
  ((SimplicialObject.Augmented.whiskering (FormalCoproduct.{v} (TopologicalSpace.Opens X)) Aᵒᵖ).obj
    (((FormalCoproduct.evalOp (TopologicalSpace.Opens X) A).obj P).rightOp)).obj
      (openCechAugmented U)

/--
概要：評価後の交代境界複体を戻すと Mathlib の同じ Čech 複体になる。
方針：各項の恒等同型と交代余面微分の対圏比較を使う。
規約：符号と次数の向きを保持する。
使われ方：TT §3、Toën §3.2 の Čech 収縮の具体的比較。
-/
def openCechCochainUnopIso :
    (AlgebraicTopology.AlternatingFaceMapComplex.obj (openCechEvaluation U P).left).unop ≅
      (cechComplexFunctor U).obj P := by
  refine HomologicalComplex.Hom.isoOfComponents (fun _ => Iso.refl _) ?_
  intro n m hnm
  have hm : n + 1 = m := hnm
  subst m
  refine Eq.trans (Category.id_comp _) (Eq.trans ?_ (Category.comp_id _).symm)
  exact (CochainComplex.of_d _ _ n).trans
    ((AlgebraicTopology.AlternatingCofaceMapComplex.d_eq_unop_d
      ((FormalCoproduct.cosimplicialObjectFunctor (FormalCoproduct.mk ι U).cech).obj P) n).trans
      (congrArg Quiver.Hom.unop (AlgebraicTopology.AlternatingFaceMapComplex.obj_d_eq
        (openCechEvaluation U P).left n)).symm)

/--
概要：全体を含む開被覆の Čech 複体は全ての正次数で完全。
方針：具体的な追加退化を評価し、収縮の対圏比較を経て同じ複体へ戻す。
規約：前層の層条件・被覆の有限性は不要。
使われ方：TT §3、Toën §3.2 のアフィン局所化後の Čech 計算。
-/
lemma splitOpenCech_exactAt (j : ι) (hj : U j = ⊤) (n : ℕ) :
    ((cechComplexFunctor U).obj P).ExactAt (n + 1) := by
  let ed := (splitOpenCechExtraDegeneracy U j hj).map
    (((FormalCoproduct.evalOp (TopologicalSpace.Opens X) A).obj P).rightOp)
  let e := ed.homotopyEquiv
  have h : (AlgebraicTopology.AlternatingFaceMapComplex.obj
      (openCechEvaluation U P).left).ExactAt (n + 1) :=
    (exactAt_iff_of_quasiIsoAt e.hom (n + 1)).mpr
      (ChainComplex.exactAt_succ_single_obj _ n)
  exact (exactAt_iff_of_quasiIsoAt
    (openCechCochainUnopIso U P).hom (n + 1)).mp h.unop

end SerrePositivity.KST.DerivedGeometry
