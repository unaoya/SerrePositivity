module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGCyclePostcomposition
public import SerrePositivity.DifferentialGraded.Module.Graded
public import SerrePositivity.DifferentialGraded.Module.Hom.HomotopyAndOperations
public import SerrePositivity.DifferentialGraded.Functor.QuasiEquivalence

/-! # Yoneda 閉射の評価と元の Hom の後合成

概要：Yoneda 像の実閉射を対象で評価すると、元の Hom の後合成鎖写像に厳密に一致する。
方針：閉射の cycle の像と、Yoneda の全次数成分の作用公式を照合する。
規約：全整数次数を保持する。使われ方：最後辺の Hom cone と加群 cone の実鎖同型。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [Small.{u} D]

/-- 元の閉射の Yoneda 像を評価した鎖写像は、元の Hom の後合成そのもの。 -/
lemma dgYonedaEvaluation_postcomposition (x : D) {y z : _root_.SerrePositivity.DifferentialGraded.ClosedCategory A D} (g : y ⟶ z) :
    (_root_.SerrePositivity.DifferentialGraded.moduleEvaluation A D x).map ((dgYoneda A D).onClosed.map g) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCyclePostcomposition A D x (_root_.SerrePositivity.DifferentialGraded.closedHomEquiv A D y z g) := by
  apply HomologicalComplex.Hom.ext
  funext k
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro f
  change ((moduleEvaluation A D x).map ((dgYoneda A D).onClosed.map g)).f k f =
    compose A (closedHomEquiv A D y z g).val f (add_zero k)
  have he := moduleEvaluation_cochain A D x ((dgYoneda A D).onClosed.map g)
  have hg : (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A)
      ((dgYoneda A D).onClosed.map g))).val =
      (yonedaHom A D y z).f 0 (closedHomEquiv A D y z g).val :=
    congrArg Subtype.val ((dgYoneda A D).closedHomEquiv_map g)
  rw [hg] at he
  have hc := congrArg (fun a => a.v k k (add_zero k) f) he
  change ((moduleEvaluation A D x).map ((dgYoneda A D).onClosed.map g)).f k f =
    (((moduleHomπ A D (representable A y) (representable A z) x).f 0
      ((yonedaHom A D y z).f 0 (closedHomEquiv A D y z g).val)).v k k (add_zero k)) f at hc
  rw [yonedaHom_element] at hc
  simpa only [ Int.zero_mul, Int.mul_zero, Int.negOnePow_zero,
    one_smul, compose] using hc

end SerrePositivity.InfinityCategories.Project.DerivedCategories
