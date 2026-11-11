module
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.PushoutShape
public import SerrePositivity.InfinityCategories.HTT.InitialAndFinalObjects.InitialBoundaryTransport
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ColimitRelativeBoundary
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorHomotopy

/-! # 図式を動かす余極限の輸送
概要：異なる固定図式の余錐でも、全余錐の関手が同型なら余極限性は保たれる。
方針：余極限性を余錐制限の相対始点境界充填に直し、可逆辺の不変性を使う。
規約：頂点だけの同型でなく余錐全体の coherent な同型を使う。
使われ方：HTT §4.3.2、固定零射への cofiber の輸送。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 概要：余錐全体の関手が同型なら、基底図式が異なっていても余極限性は保たれる。
方針：余錐制限の相対始点境界充填を関手頂点の同型で移す。
規約：X は quasicategory、K は任意。使われ方：異なる図式上の普遍余錐の比較。 -/
lemma IsColimitCone.of_functorIso {K X : SSet.{u}} [Quasicategory X]
    {p q : K ⟶ X} {c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone p} {d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone q}
    (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c) (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso c.val d.val) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone d := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.isColimitCone_of_initialBoundaryLifting_coconeRestriction d
  exact _root_.SerrePositivity.InfinityCategories.HTT.InitialAndFinalObjects.InitialBoundaryLifting.of_vertexIso (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeRestriction K X) hc.initialBoundaryLifting e

/-- 概要：同型な全余錐の余極限性は同値。
方針：同型と逆同型の両方に輸送を適用する。
規約：固定図式は異なっていてよい。使われ方：cofiber の形状の変更の認証。 -/
lemma isColimitCone_iff_of_functorIso {K X : SSet.{u}} [Quasicategory X]
    {p q : K ⟶ X} (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone p) (d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone q)
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso c.val d.val) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone d :=
  ⟨fun h => IsColimitCone.of_functorIso h e,
    fun h => IsColimitCone.of_functorIso h e.symm⟩

/-- 概要：正方形の図式の関手同型は押し出し性を保つ。
方針：span の余錐と正方形の同型で前合成して、全余錐の普遍性を移す。
規約：単なる四頂点の同型の族は仮定しない。
使われ方：同じ射の異なる零角を持つ cofiber の比較。 -/
lemma IsPushoutSquare.of_functorIso {X : SSet.{u}} [Quasicategory X]
    {F G : (Δ[1] ⊗ Δ[1] : SSet.{u}) ⟶ X}
    (hF : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare F) (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso F G) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare G := by
  exact IsColimitCone.of_functorIso hF (e.precomp _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanCoconeSquareIso.hom)

end SerrePositivity.KST.SConstruction
