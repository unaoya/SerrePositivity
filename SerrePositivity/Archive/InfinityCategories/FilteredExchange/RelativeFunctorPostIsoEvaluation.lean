module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.RelativeFunctorPostVertexIso
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.RelativeFunctorCurryIsoPresentation
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorIsoPointEvaluation

/-!
概要：元の豊穣後合成の指定同型の成分を、同じ実始域射での前合成へ値まで戻す。
方針：全相対関手空間での一点評価と元の相対前合成の厳密な一致を使う。
規約：元の指定値を保持。使われ方：零面の三角形比較を共通の始点比較で輸送する。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 豊穣後合成の実始域射での一点評価は、元の同じ相対前合成そのもの。 -/
lemma relativeFunctorPostHom_evaluate_vertex {B C E Q : SSet.{u}}
    (q : E ⟶ B) (r : Q ⟶ B) (s : C ⟶ E) :
    relativeFunctorPostHom (Over.mk (s ≫ q)) (Over.mk q) (Over.mk r) ≫
        evaluateFunctorAt (relativeFunctorVertex q (s ≫ q) s rfl) =
      relativeFunctorPre r q s := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro f
  apply Subtype.ext
  rfl

/-- 後合成の元の指定同型の成分は、同じ元の指定頂点同型の実始域射での前合成の値。 -/
lemma relativeFunctorPostVertexIso_app_heq_pre {B C E Q : SSet.{u}}
    (p : C ⟶ B) (q : E ⟶ B) (r : Q ⟶ B) [LeftFibration q] [LeftFibration r]
    (f g : E ⟶ Q) (hf : f ≫ r = q) (hg : g ≫ r = q)
    (e : VertexIso (relativeFunctorVertex r q f hf) (relativeFunctorVertex r q g hg))
    (s : C ⟶ E) (hs : s ≫ q = p) :
    HEq ((relativeFunctorPostVertexIso p q r f g hf hg e).app (relativeFunctorVertex q p s hs))
      (VertexIso.map e (relativeFunctorPre r q s)) := by
  subst p
  let R := relativeFunctorPostHom (Over.mk (s ≫ q)) (Over.mk q) (Over.mk r)
  let x := relativeFunctorVertex q (s ≫ q) s rfl
  let e' := relativeFunctorPostVertexIso (s ≫ q) q r f g hf hg e
  have hx := relativeFunctorPostHom_vertex (Over.mk (s ≫ q)) (Over.mk q) (Over.mk r)
    (Over.homMk f hf)
  have hy := relativeFunctorPostHom_vertex (Over.mk (s ≫ q)) (Over.mk q) (Over.mk r)
    (Over.homMk g hg)
  have hm := vertexIso_map_heq_of_heq e' (VertexIso.map e R) hx.symm hy.symm
    (relativeFunctorPostVertexIso_heq_map (s ≫ q) q r f g hf hg e) (evaluateFunctorAt x)
  exact (functorIso_app_heq_evaluate e' x).trans (hm.trans
    ((heq_of_eq (vertexIso_map_comp e R (evaluateFunctorAt x))).trans
      (vertexIso_map_heq e (relativeFunctorPostHom_evaluate_vertex q r s))))

end SerrePositivity.InfinityCategories.F2
