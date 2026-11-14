module
public import SerrePositivity.KST.SConstruction.SquareFrameHomotopyPostcomp
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.KanHomotopyEquivalence
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.VertexTransport.FunctorIsoTransport
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.MappingSpaces.FunctorIsoWhiskerHom

/-!
概要：元全ホモトピーの厳密な制限と射の類の保持から、指定全比較そのものを回収する。
方針：同じ前合成の辺と元代表の類を照合する。
規約：存在型へ弱めない。使われ方：全右面比較の指定三境界と二胞体の回収。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet InfinityCategories
open scoped Simplicial

/-- 概要：元全比較の制限は元側面の指定比較そのもの。
方針：元全ホモトピーの厳密制限を前合成の辺の類で検出する。
規約：全比較・元端点等号を保持。使われ方：指定境界の厳密回収。 -/
lemma specifiedHomotopyRestrictionIso {A B X : SSet.{u}}
    {f g : A ⟶ X} {f' g' : B ⟶ X}
    (H : SSet.Homotopy f g) (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f g)
    (he : e.hom = Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy H))
    (q : B ⟶ A) (hf : q ≫ f = f') (hg : q ≫ g = g')
    (H' : SSet.Homotopy f' g') (e' : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f' g')
    (he' : e'.hom = Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy H'))
    (hh : (q ▷ (Δ[1] : SSet.{u})) ≫ H.h = H'.h) :
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq (e.precomp q) hf hg = e' := by
  subst f' g'
  change e.precomp q = e'
  apply Iso.ext
  rw [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_precomp_hom, he, he']
  change Truncated.HomotopyCategory.homMk
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy H).map ((truncation 2).map ((pre q).app X))) =
      Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy H')
  apply congrArg Truncated.HomotopyCategory.homMk
  apply Truncated.Edge.ext
  change ((pre q).app X).app (Opposite.op ⦋1⦌)
    (SSet.yonedaEquiv (curry H.h)) = SSet.yonedaEquiv (curry H'.h)
  rw [← SSet.yonedaEquiv_comp, curry_pre_app, hh]
/-- 概要：元指定全比較の同じ後合成は元後合成ホモトピーの射の類。
方針：元関手辺の後合成と curry の自然性を使う。
規約：元全比較の値を保持。使われ方：Cat^perf 辺比較の StableInfinity 像。 -/
lemma specifiedHomotopyPostcomp_class {A X Y : SSet.{u}} {f g : A ⟶ X}
    (H : SSet.Homotopy f g) (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f g)
    (he : e.hom = Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy H))
    (k : X ⟶ Y) : (e.postcomp k).hom =
      Truncated.HomotopyCategory.homMk
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (specifiedHomotopyPostcomp H k)) := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_postcomp_hom, he]
  change Truncated.HomotopyCategory.homMk
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy H).map ((truncation 2).map ((ihom A).map k))) = _
  apply congrArg Truncated.HomotopyCategory.homMk
  apply Truncated.Edge.ext
  change ((ihom A).map k).app (Opposite.op ⦋1⦌) (SSet.yonedaEquiv (curry H.h)) =
    SSet.yonedaEquiv (curry (H.h ≫ k))
  rw [← SSet.yonedaEquiv_comp, curry_natural_right]

/-- 概要：端点表示を変えた同じ全ホモトピーの指定比較は元同型の表示変更そのもの。
方針：元端点等号を消去し、同じ全写像から同じ関手辺の類を回収する。
規約：元全比較を選び直さない。使われ方：元正規形の辺比較と実四辺の照合。 -/
lemma specifiedHomotopyEndpointIso {A X : SSet.{u}} {f g f' g' : A ⟶ X}
    (H : SSet.Homotopy f g) (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f g)
    (he : e.hom = Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy H))
    (hf : f = f') (hg : g = g') (H' : SSet.Homotopy f' g')
    (hh : H.h = H'.h) :
    (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq e hf hg).hom =
      Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy H') := by
  subst f' g'
  change e.hom = _
  rw [he]
  apply congrArg Truncated.HomotopyCategory.homMk
  apply Truncated.Edge.ext
  exact congrArg (fun q : A ⊗ Δ[1] ⟶ X => SSet.yonedaEquiv (curry q)) hh
end SerrePositivity.KST.SConstruction
