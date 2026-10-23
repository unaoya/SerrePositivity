module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.ScaffoldPullbackMarkedEquivalence
public import SerrePositivity.InfinityCategories.F1.Cocartesian.ScaffoldPullbackNaturality
public import SerrePositivity.InfinityCategories.F1.Cocartesian.PullbackHomFunctor

/-!
概要：部分底上の scaffold の指定辺保存 Hom の実際の制限。
方針：同じ scaffold 比較の自然性と元の底変換の辺保存で、指定辺の逆像を保つ。
規約：制限の射は元の pullback 関手の射そのもの。
使われ方：元の辺保存 Hom 比較を境界固定 fiber へ制限する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories
variable {C : Type u} [Category.{u} C] {E F : SSet.{u}}
  (p : E ⟶ nerve C) [CocartesianFibration p] (q : F ⟶ nerve C)
  {a b : Over (nerve C)} (f : a ⟶ b)

/-- 部分底の射は、同じ scaffold 比較の像で定めた実際の指定辺を保つ。 -/
lemma cocartesianScaffoldPullbackMark_map
    (e : (pullback a.hom
      (simplicialReplacementProjection (kanCocartesianStrictTransportDiagram p))) _⦋1⦌)
    (he : e ∈ cocartesianScaffoldPullbackMark p a) :
    ((overPullbackUnderlying
        (simplicialReplacementProjection (kanCocartesianStrictTransportDiagram p))).map f).app
      (Opposite.op ⦋1⦌) e ∈ cocartesianScaffoldPullbackMark p b := by
  have hn := congrArg (fun k ↦ k.left.app (Opposite.op ⦋1⦌) e)
    (cocartesianScaffoldPullbackOverMap_naturality p f)
  change (cocartesianScaffoldPullbackOverMap p b).left.app _
      (((overPullbackUnderlying
        (simplicialReplacementProjection (kanCocartesianStrictTransportDiagram p))).map f).app _ e) =
    ((overPullbackUnderlying p).map f).app _
      ((cocartesianScaffoldPullbackOverMap p a).left.app _ e) at hn
  change IsCocartesianEdge (pullback.fst b.hom p) _
  rw [hn]
  exact isCocartesianEdge_overPullback_map p f _ he

/-- 部分底上の指定辺保存 scaffold Hom の実際の制限。 -/
def cocartesianScaffoldPullbackMarkedHomPre :
    cocartesianScaffoldPullbackMarkedHom p q b ⟶ cocartesianScaffoldPullbackMarkedHom p q a :=
  markedCocartesianFunctorPre q
    ((Over.pullback (simplicialReplacementProjection (kanCocartesianStrictTransportDiagram p)) ⋙
      Over.map (simplicialReplacementProjection (kanCocartesianStrictTransportDiagram p))).map f)
    (cocartesianScaffoldPullbackMark p a) (cocartesianScaffoldPullbackMark p b)
    (cocartesianScaffoldPullbackMark_map p f)

/-- 同じ scaffold Hom 制限は、元の全相対 Hom の制限を保持する。 -/
lemma cocartesianScaffoldPullbackMarkedHomPre_ι :
    cocartesianScaffoldPullbackMarkedHomPre p q f ≫
      markedCocartesianFunctorInclusion q _ (cocartesianScaffoldPullbackMark p a) =
    markedCocartesianFunctorInclusion q _ (cocartesianScaffoldPullbackMark p b) ≫
      relativeFunctorOverPre q
        ((Over.pullback (simplicialReplacementProjection (kanCocartesianStrictTransportDiagram p)) ⋙
          Over.map (simplicialReplacementProjection (kanCocartesianStrictTransportDiagram p))).map f) :=
  markedCocartesianFunctorPre_ι q _ _ _ _

/-- 元の辺保存 Hom の同じ scaffold 前合成は、部分底の制限と厳密に可換。 -/
lemma cocartesianScaffoldPullbackMarkedPre_naturality :
    cocartesianPullbackHomPre p q f ≫ cocartesianScaffoldPullbackMarkedPre p q a =
      cocartesianScaffoldPullbackMarkedPre p q b ≫
        cocartesianScaffoldPullbackMarkedHomPre p q f := by
  apply (cancel_mono
    (fullSubcomplexOnVertices _ (markedCocartesianFunctorPredicate q _
      (cocartesianScaffoldPullbackMark p a))).ι).mp
  change _ ≫ markedCocartesianFunctorInclusion q _ (cocartesianScaffoldPullbackMark p a) =
    _ ≫ markedCocartesianFunctorInclusion q _ (cocartesianScaffoldPullbackMark p a)
  conv_lhs =>
    rw [Category.assoc, cocartesianScaffoldPullbackMarkedPre_ι, ← Category.assoc,
      cocartesianPullbackHomPre_ι, Category.assoc]
  conv_rhs =>
    rw [Category.assoc, cocartesianScaffoldPullbackMarkedHomPre_ι]
    simp only [CategoryTheory.Functor.comp_obj, Over.map_obj_hom, Over.pullback_obj_hom]
    rw [← Category.assoc, cocartesianScaffoldPullbackMarkedPre_ι p q b, Category.assoc]
  change _ ≫ (relativeFunctorOverPre q _ ≫ relativeFunctorOverPre q _) =
    _ ≫ (relativeFunctorOverPre q _ ≫ relativeFunctorOverPre q _)
  rw [← relativeFunctorOverPre_comp, ← relativeFunctorOverPre_comp,
    cocartesianScaffoldPullbackOverMap_naturality]

end SerrePositivity.InfinityCategories
