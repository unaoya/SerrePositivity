module

public import SerrePositivity.InfinityCategories.F2.Presentable.RepresentedRestrictionInversion
public import SerrePositivity.InfinityCategories.F1B.Localization.ReflectiveUnitInvertible
public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.SmallUnstraighteningPointFiberEvaluation

/-!
概要：反映から得た表現対象の全 Hom は元の反映単位を反転する。
方針：反映で写した単位の全可逆性を評価し、同じ実辺の反対像へ移す。
規約：元の単位成分を表す辺を指定して保持する。
使われ方：表現対象の局所性を写像空間の前合成で検査する直前の界面。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable

/-- 概要：元の反映単位の各点の像は reflector によって可逆になる。
方針：全単位の後合成の可逆性を同じ頂点で評価し、評価と後合成の可換性を使う。
規約：任意の同型な比較に単位成分を置き換えない。
使われ方：指定単位を表す実辺の反転性。 -/
lemma reflectiveUnit_map_isIso {X : SSet.{u}} [Quasicategory X]
    {P : X _⦋0⦌ → Prop} (r : ReflectiveSubcategory X P) (x : X _⦋0⦌) :
    IsIso ((hoFunctor.map r.reflector).toFunctor.map (qcatUnitComponent r.unit x)) := by
  have : IsIso ((hoFunctor.map ((ihom X).map r.reflector)).toFunctor.map r.unit) :=
    r.adjunction.unit_postcompLeft_isIso
  have he : IsIso ((hoFunctor.map ((ihom X).map r.reflector ≫
      evaluateFunctorAt x)).toFunctor.map r.unit) := by
    rw [CategoryTheory.Functor.map_comp]
    rw [Cat.Hom.comp_map]
    infer_instance
  rw [evaluateFunctorAt_post] at he
  have : IsIso ((hoFunctor.map r.reflector).toFunctor.map
      ((hoFunctor.map (evaluateFunctorAt (Y := X) x)).toFunctor.map r.unit)) := by
    rw [CategoryTheory.Functor.map_comp] at he
    exact he
  unfold qcatUnitComponent functorHomEvaluate
  simp only [CategoryTheory.Functor.map_comp]
  infer_instance

/-- 概要：反映へ引き戻した前層の全表現可能 Hom は元の単位の反対辺を反転する。
方針：指定単位の reflector による像の可逆性を、表現された制限前層へ移す。
規約：元の単位成分との一致を明示し、局所性を追加入力にしない。
使われ方：局所対象の前合成判定による表現対象の下降。 -/
lemma representedReflectiveUnit_inverts_op_edge
    {X : SSet.{u + 1}} [Quasicategory X] {P : X _⦋0⦌ → Prop}
    (r : ReflectiveSubcategory X P)
    (F : (fullSubcomplexOnVertices X P : SSet.{u + 1}).op ⟶ SpaceInfinity.{u})
    (z : X _⦋0⦌)
    (h : FunctorIso (representablePresheafInfinity z)
      ((SSet.uliftFunctor.{u + 2, u + 1}).map (SSet.opFunctor.map r.reflector ≫ F) ≫
        Compact.spaceUniverseDiagram))
    (x : X _⦋0⦌)
    (e : Truncated.Edge (X := (truncation 2).obj X) x (r.localization.app _ x))
    (he : Truncated.HomotopyCategory.homMk e = qcatUnitComponent r.unit x) :
    IsInvertibleEdge ((uliftTruncatedEdge.{u + 1, u + 2} (edgeOp e)).map
      ((truncation 2).map (representablePresheafInfinity z))) := by
  apply representedRestriction_inverts_op_edge r.reflector F z h e
  change IsIso ((hoFunctor.map r.reflector).toFunctor.map
    (Truncated.HomotopyCategory.homMk e))
  rw [he]
  exact reflectiveUnit_map_isIso r x

end SerrePositivity.InfinityCategories.F2.Presentable
