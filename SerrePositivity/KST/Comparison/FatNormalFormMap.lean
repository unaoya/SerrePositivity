module

public import SerrePositivity.KST.Comparison.FatNormalFormEquiv
public import SerrePositivity.KST.Comparison.FatRealizationFunctor

/-!
# fat realization の標準形の自然性

概要：二重単体集合の射は標準形の全射を保ち、行の元だけに作用する。
方針：像分解に沿う自然性と、余等化子の全射性で一般の元へ移す。
規約：Segal 1974 Proposition 1.6、Appendix A の fat realization の計算。
使われ方：fat realization の写像と骨格の各次数の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.Comparison
open CategoryTheory Limits Opposite MonoidalCategory
open scoped Simplicial ConcreteCategory

/--
概要：二重単体集合の射による標準形の写像。
方針：全射の終域と全射を固定し、行の元へ自然変換を適用する。
規約：標準形の次数は変わらない。
使われ方：余等化子の写像の次数ごとの計算。
-/
def fatNormalFormMap {F G : SimplexCategoryᵒᵖ ⥤ SSet.{u}} (α : F ⟶ G)
    (d : SimplexCategoryᵒᵖ) (p : FatNormalForm F d) : FatNormalForm G d where
  degree := p.degree
  epi := p.epi
  epi_property := p.epi_property
  simplex := (α.app (op p.degree)).app d p.simplex

/--
概要：行の正規化は二重単体集合の射と可換である。
方針：像の包含への自然性を同じ内側次数で評価する。
規約：元の標準単体の射は任意。
使われ方：余等化子の写像の正規化の自然性。
-/
theorem fatNormalize_map {F G : SimplexCategoryᵒᵖ ⥤ SSet.{u}} (α : F ⟶ G)
    (d : SimplexCategoryᵒᵖ) {n : SimplexCategory} (x : (F.obj (op n)).obj d)
    (t : d.unop ⟶ n) :
    fatNormalFormMap α d (fatNormalize F d x t) =
      fatNormalize G d ((α.app (op n)).app d x) t := by
  have h := congrArg (fun q => q.app d x) (α.naturality (image.ι t).op)
  exact congrArg (fun y => FatNormalForm.mk (image t) (factorThruImage t) inferInstance y) h

/--
概要：標準形から各行へ戻す操作は二重単体集合の射と可換である。
方針：fat realization の写像を各行へ制限して計算する。
規約：全射な添字は両辺で同じ。
使われ方：標準形との同値の自然性。
-/
theorem fatNormalFormRealize_map {F G : SimplexCategoryᵒᵖ ⥤ SSet.{u}} (α : F ⟶ G)
    (d : SimplexCategoryᵒᵖ) (p : FatNormalForm F d) :
    (fatRealizationMap α).app d (fatNormalFormRealize F d p) =
      fatNormalFormRealize G d (fatNormalFormMap α d p) :=
  congrArg (fun q => q.app d (p.simplex, SSet.stdSimplex.objEquiv.symm p.epi))
    (fatRealizationInclusion_map α p.degree.len)

/--
概要：fat realization の写像は、正規化した標準形の行の元だけを写す。
方針：元を標準形からの復元で表示し、復元と正規化の両逆性を使う。
規約：全ての次数と元での等式。
使われ方：fat realization の写像の単射性・成分の計算。
-/
theorem fatDegreeNormalize_map {F G : SimplexCategoryᵒᵖ ⥤ SSet.{u}} (α : F ⟶ G)
    (d : SimplexCategoryᵒᵖ) (y : (fatRealization F).obj d) :
    fatDegreeNormalize G d ((fatRealizationMap α).app d y) =
      fatNormalFormMap α d (fatDegreeNormalize F d y) := by
  rw [← fatNormalFormRealize_degreeNormalize F d y, fatNormalFormRealize_map,
    fatDegreeNormalize_realize]
  rw [fatDegreeNormalize_realize]

end SerrePositivity.KST.Comparison
