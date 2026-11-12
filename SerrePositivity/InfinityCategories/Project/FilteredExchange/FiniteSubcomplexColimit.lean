module

public import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex
public import Mathlib.AlgebraicTopology.SimplicialSet.SubcomplexEvaluation
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FiniteSubcomplexes

/-!
概要：単体集合はその有限部分複体の filtered 余極限である。
方針：各単体の生成する有限部分複体で上限が全体であることを示し、包含関手で写す。
規約：余極限の頂点を元の単体集合、各脚を元の包含に固定する。
使われ方：有限境界から Kan 置換への写像の有限部分への因子分解。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.FilteredExchange

/-- 概要：有限部分複体を元の部分複体の圏へ含める関手。
方針：有限性の証明を忘れ、包含射をそのまま使う。
規約：全ての対象・射は元の包含。使われ方：filtered な部分複体の余極限。 -/
def finiteSubcomplexInclusion (X : SSet.{u}) : _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.FiniteSubcomplex X ⥤ X.Subcomplex where
  obj A := A.val
  map f := homOfLE (leOfHom f)

/-- 概要：全ての有限部分複体の最小上界は全体。
方針：各単体はそれ自身が生成する有限部分複体に属する。
規約：各次数の任意の単体を扱う。使われ方：有限部分複体の余極限の頂点の同定。 -/
lemma isLUB_finiteSubcomplexInclusion (X : SSet.{u}) :
    IsLUB (Set.range (finiteSubcomplexInclusion X).obj) ⊤ := by
  refine ⟨?_, ?_⟩
  · rintro _ ⟨A, rfl⟩
    exact le_top
  · intro B hB n x _
    obtain ⟨⟨n⟩⟩ := n
    have h : Subcomplex.ofSimplex x ≤ B :=
      hB ⟨⟨Subcomplex.ofSimplex x, inferInstance⟩, rfl⟩
    exact h _ (Subcomplex.mem_ofSimplex_obj x)

/-- 概要：有限部分複体を単体集合の圏へ送る filtered 図式。
方針：有限部分複体の包含関手と単体集合への忘却関手を合成する。
規約：添字の小ささと filtered 性は有限部分複体の型が与える。
使われ方：有限表示性の適用先となる実際の図式。 -/
def finiteSubcomplexDiagram (X : SSet.{u}) : _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.FiniteSubcomplex X ⥤ SSet.{u} :=
  finiteSubcomplexInclusion X ⋙ Subcomplex.toSSetFunctor

/-- 概要：元の単体集合を頂点とする有限部分複体の余錐。
方針：各部分複体の元の包含を脚として用いる。
規約：頂点は同型な別対象に置き換えない。使われ方：元の射を保つ因子分解。 -/
def finiteSubcomplexCocone (X : SSet.{u}) : Cocone (finiteSubcomplexDiagram X) where
  pt := X
  ι := { app A := A.val.ι }

/-- 概要：元の包含を脚とする有限部分複体の余錐は余極限。
方針：部分複体の最小上界の余極限性と包含関手の filtered 余極限保存を合成する。
規約：通常の単体集合の圏の余極限を証明する。
使われ方：有限部分を経由する有限境界の因子分解。 -/
def finiteSubcomplexCocone_isColimit (X : SSet.{u}) :
    IsColimit (finiteSubcomplexCocone X) := by
  let c := Preorder.colimitCoconeOfIsLUB (finiteSubcomplexInclusion X)
    (isLUB_finiteSubcomplexInclusion X)
  have hc := isColimitOfPreserves Subcomplex.toSSetFunctor c.isColimit
  exact IsColimit.ofIsoColimit hc (Cocone.ext (Subcomplex.topIso X) (by intro A; rfl))

end SerrePositivity.InfinityCategories.Project.FilteredExchange
