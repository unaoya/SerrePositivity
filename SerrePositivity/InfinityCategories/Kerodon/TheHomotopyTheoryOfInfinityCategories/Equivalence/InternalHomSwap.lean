module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.FullSubcomplexInternalHom
public import Mathlib.CategoryTheory.Monoidal.Closed.InternalCurrying

/-!
概要：二重の内部 Hom の二変数を交換する同型。
方針：内部 currying と直積の対称性を合成する。
規約：任意の単体集合の三対象を扱う。
使われ方：Kerodon §4.5.3（Tag 032Y）、§4.5.5（Tag 01F6） の可逆 path と関手単体集合の比較。

対応節は Kerodon 4.5（Tag 01DE）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence

/-- 概要：二つの始域を持つ内部 Hom の順序を交換する同型。
方針：一度 uncurry して直積の二因子を交換し、再び curry する。
規約：quasicategory 性は不要。
使われ方：Kerodon §4.5.3（Tag 032Y） の path と内部 Hom の順序の交換。 -/
def internalHomSwapIso (A B X : SSet.{u}) :
    (ihom A).obj ((ihom B).obj X) ≅ (ihom B).obj ((ihom A).obj X) :=
  (ihomCurryIso B A X).symm ≪≫
    (internalHom.mapIso (β_ A B).op).app X ≪≫ ihomCurryIso A B X

/-- 概要：二重の内部 Hom の交換は実際の射の転置を頂点で実現する。
方針：内部 currying と対称性を各次数で計算する。
規約：f は A から B 上の関手単体集合への射。
使われ方：Kerodon §4.5.3（Tag 032Y） の可逆性条件の対応。 -/
lemma internalHomSwapIso_functorVertex (A B X : SSet.{u}) (f : A ⟶ (ihom B).obj X) :
    (internalHomSwapIso A B X).hom.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex f) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (curry ((β_ A B).hom ≫ uncurry f)) := by
  rfl

/-- 概要：区間と K の内部 Hom の交換は各頂点での評価による区間の辺に対応する。
方針：元の頂点を実際の区間からの射で表し、転置と評価を計算する。
規約：K と X の quasicategory 性は不要。
使われ方：Kerodon §4.5.3（Tag 032Y） の関手単体集合の辺の可逆性の比較。 -/
lemma internalHomSwapIso_interval_evaluate (K X : SSet.{u})
    (v : ((ihom (Δ[1] : SSet.{u})).obj ((ihom K).obj X)) _⦋0⦌) (k : K _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalFunctorVertexEdge ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := (ihom (Δ[1] : SSet.{u})).obj X) k).app
      (Opposite.op ⦋0⦌) ((internalHomSwapIso Δ[1] K X).hom.app (Opposite.op ⦋0⦌) v)) =
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := X) k).app (Opposite.op ⦋1⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalFunctorVertexEdge v) := by
  obtain ⟨f, rfl⟩ := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv Δ[1] ((ihom K).obj X)).surjective v
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalFunctorVertexEdge ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt k).app (Opposite.op ⦋0⦌)
    ((internalHomSwapIso Δ[1] K X).hom.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex f))) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := X) k).app (Opposite.op ⦋1⦌)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalFunctorVertexEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex f))
  rw [internalHomSwapIso_functorVertex, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt_functorVertex,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalFunctorVertexEdge_functorVertex]
  rfl

/-- 概要：二重の内部 Hom の交換後の評価は交換前の評価と一致する。
方針：二回の curry と評価を各次数で計算する。
規約：a は最初の始域の任意の頂点。
使われ方：Kerodon §4.5.3（Tag 032Y） の path の両端の対応。 -/
lemma internalHomSwapIso_evaluate (A B X : SSet.{u}) (a : A _⦋0⦌) :
    (internalHomSwapIso A B X).hom ≫ (ihom B).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := X) a) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := (ihom B).obj X) a := by
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro F
  apply CategoryTheory.Functor.functorHom_ext
  intro e α
  apply ConcreteCategory.hom_ext
  intro b
  change (F.app e (α ≫ 𝟙 e) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant a e.unop.len)).app e (𝟙 e)
      (B.map (𝟙 e) b) =
    (F.app d (𝟙 d) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant a d.unop.len)).app e α b
  rw [Category.comp_id, CategoryTheory.Functor.map_id_apply]
  have hn := ConcreteCategory.congr_hom (F.naturality α (𝟙 d))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant a d.unop.len)
  have he := congrArg (fun G : ((ihom B).obj X).obj e ↦ G.app e (𝟙 e) b) hn
  change (F.app e (𝟙 d ≫ α) (A.map α (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant a d.unop.len))).app e (𝟙 e) b =
    (F.app d (𝟙 d) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant a d.unop.len)).app e (α ≫ 𝟙 e) b at he
  have hc : A.map α (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant a d.unop.len) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant a e.unop.len := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant_pullback a α.unop
  simpa only [Category.id_comp, Category.comp_id, hc] using he

/-- 概要：二重の内部 Hom の交換は第二始域での前合成と可換。
方針：転置した内部 Hom の各次数を計算する。
規約：i は任意の単体集合の射。
使われ方：Kerodon §4.5.5（Tag 01F6） の制限に対する相対 path。 -/
lemma internalHomSwapIso_pre {A B C X : SSet.{u}} (i : B ⟶ C) :
    (ihom A).map ((pre i).app X) ≫ (internalHomSwapIso A B X).hom =
      (internalHomSwapIso A C X).hom ≫ (pre i).app ((ihom A).obj X) := by
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro F
  apply CategoryTheory.Functor.functorHom_ext
  intro e α
  apply ConcreteCategory.hom_ext
  intro b
  apply CategoryTheory.Functor.functorHom_ext
  intro t β
  apply ConcreteCategory.hom_ext
  intro a
  change (F.app t (α ≫ β) a).app t (𝟙 t) (i.app t (B.map β b)) =
    (F.app t (α ≫ β) a).app t (𝟙 t) (C.map β (i.app e b))
  exact congrArg (fun z : C.obj t ↦ (F.app t (α ≫ β) a).app t (𝟙 t) z)
    (ConcreteCategory.congr_hom (i.naturality β) b)

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence
