module
public import SerrePositivity.KST.SConstruction.PerfectLaxQuotientProductSquare
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.SquareHomotopyCategory

/-! # 実積へ移送した Cat^perf 比較図式の四頂点
概要：全図式を移した後も、指定した元の BF 値・実積を四角に厳密に回収する。
方針：延長の各頂点と元の指定頂点同型の終点を照合する。
規約：全正方形の同型と同じ延長を使う。使われ方：四辺の元の射への正規化。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet Spectra
open SerrePositivity.InfinityCategories LocalizingInvariants
open scoped Simplicial
namespace PerfectLaxQuotient
local instance productVerticesSimplicialCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory
variable {C D B : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} {p : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap C B} {q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap D B}
  (d : PerfectLaxQuotient p q)
  {F : perfectStableInfinity.{u} ⟶ Sp.{u}} (hF : IsPerfectLocalizingInvariant F)

/-- 同じ全図式の延長の四角は、元の指定した頂点そのもの。 -/
lemma productSquare_vertex_at (a b : Fin 2) : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex (d.productSquare hF) a b =
    (d.productCornerIso hF a b).1 := by
  have hv := DiagramVertexPaths.Extension.target_vertex_ofIso (d.productVertexIsos hF)
    (d.productExtension hF) (stdSimplex.obj₀Equiv.symm a, stdSimplex.obj₀Equiv.symm b)
  refine hv.trans ?_
  change (d.productCornerIso hF
    (stdSimplex.obj₀Equiv.{u + 1} (stdSimplex.obj₀Equiv.symm a))
    (stdSimplex.obj₀Equiv.{u + 1} (stdSimplex.obj₀Equiv.symm b))).1 = _
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]

/-- 移送後の左下は元の左端の同じ BF 表示。 -/
lemma productSquare_vertex00 : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex (d.productSquare hF) 0 0 =
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (perfectInvariantSpectrum F (perfectStableVertex d.left d.left_complete)) :=
  d.productSquare_vertex_at hF 0 0

/-- 移送後の左上は元の商の完備化先の同じ BF 表示。 -/
lemma productSquare_vertex01 : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex (d.productSquare hF) 0 1 =
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (perfectInvariantSpectrum F d.sequence.rightVertex) :=
  d.productSquare_vertex_at hF 0 1

/-- 移送後の右下は、元の C・D の値の実 BF 積。 -/
lemma productSquare_vertex10 : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex (d.productSquare hF) 1 0 =
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (Binary.obj
      (perfectInvariantSpectrum F (perfectStableVertex C d.c_complete))
      (perfectInvariantSpectrum F (perfectStableVertex D d.d_complete))) :=
  d.productSquare_vertex_at hF 1 0

/-- 移送後の右上は、元の商の完備化先の値の実 BF 二重積。 -/
lemma productSquare_vertex11 : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex (d.productSquare hF) 1 1 =
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (Binary.obj
      (perfectInvariantSpectrum F d.sequence.rightVertex)
      (perfectInvariantSpectrum F d.sequence.rightVertex)) :=
  d.productSquare_vertex_at hF 1 1

end PerfectLaxQuotient
end SerrePositivity.KST.SConstruction
