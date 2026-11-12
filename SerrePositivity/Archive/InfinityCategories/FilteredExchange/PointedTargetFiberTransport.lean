module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.PointedSectionTargetFiber
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.FunctorIsoTransport
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.FunctorIsoWhiskerComposition
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FunctorIsoChainTransport

/-!
概要：辺の等式表示と指定同型の端点補正を、終点 fiber への後合成と交換する。
方針：与えられた等式だけを消去し、同じ指定同型の合成則を使う。
規約：同型の HEq から端点の等式は取り出さない。使われ方：native 二脚の共通像。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 指定同型の端点補正は、後合成後も同じ指定同型を保つ。 -/
lemma functorIsoOfEq_postcomp_heq {A X Y : SSet.{u}} {a b a' b' : A ⟶ X}
    (e : FunctorIso a b) (ha : a = a') (hb : b = b') (p : X ⟶ Y) :
    HEq ((functorIsoOfEq e ha hb).postcomp p) (e.postcomp p) := by
  subst a' b'
  rfl

/-- 二段の後合成と端点補正も、同じ一段の後合成へまとめられる。 -/
lemma functorIsoOfEq_postcomp_postcomp_heq {A X Y Z : SSet.{u}} {a b a' b' : A ⟶ X}
    (e : FunctorIso a b) (ha : a = a') (hb : b = b') (p : X ⟶ Y) (q : Y ⟶ Z) :
    HEq (((functorIsoOfEq e ha hb).postcomp p).postcomp q) (e.postcomp (p ≫ q)) := by
  subst a' b'
  exact heq_of_eq (functorIso_postcomp_postcomp e p q)

/-- 辺の表示だけを等式で変えた後の終点評価は、元の同じ終点評価。 -/
lemma pointedSectionTargetFiber_transport {B : SSet.{u}}
    (J : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}) (b : B _⦋0⦌)
    {e e' : (Δ[1] : SSet.{u + 1}) ⟶ SpaceInfinity.{u}} (h : e = e')
    (hv : e.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm 1) =
      J.app (Opposite.op ⦋0⦌) (ULift.up b))
    (hv' : e'.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm 1) =
      J.app (Opposite.op ⦋0⦌) (ULift.up b)) :
    eqToHom (congrArg (relativeFunctorSpace pointedSpaceProjection) h) ≫
      pointedSectionTargetFiber J b e' hv' = pointedSectionTargetFiber J b e hv := by
  subst e'
  simp

end SerrePositivity.InfinityCategories.F2
