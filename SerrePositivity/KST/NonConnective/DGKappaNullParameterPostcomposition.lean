module
public import SerrePositivity.KST.NonConnective.DGKappaResolvedConnectiveSquare
public import SerrePositivity.DifferentialGraded.Quotient.DerivedComparison.Filtration

/-!
概要：同じ実零角の選択収縮に、D の全パラメータ後合成延長を代入する。
方針：元の核→実懸垂の指定収縮を固定したまま、任意のパラメータ複体の変換を商へ延長する。
規約：ε 整合は D の実証明を消費。全入力四角形族・Morita/P 自然性は主張しない。
使われ方：K-7 c4・c5 の元の零角辺に対する後合成部品。
-/
@[expose] public section
noncomputable section
universe u v w
open CategoryTheory MonoidalCategory
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction
namespace SerrePositivity.KST.NonConnective
variable (R : Type u) [CommRing R] (D : PerfDGInput.{u, max (u + 1) v} R)
  {κ : Cardinal.{u}} (I : DGKappaConeInput R D κ)
  {T : Type w} [DGCategory R T] {P : Complex R}
  {H H' : DGFunctor R (dgKappaSuspensionKInput R D I) T}
  (τ : GradedNatTrans ((Center.ofBraided (Complex R)).obj P) H H')

/-- 同じ零角の元の収縮を変えず、全次数の後合成変換を元の全対象商へ延長する。 -/
def dgKappaNullParameterPostcomposition :=
  DGQuotient.parameterExtension_postcomposition R (dgKappaResolvedKernelContraction R D I) τ

/-- 全対象商の各元での成分は、元の同じ後合成変換の成分そのもの。 -/
theorem dgKappaNullParameterPostcomposition_app
    (x : DGQuotient.QuotientObject (dgKappaResolvedKernelKInput R D I) Set.univ) :
    (dgKappaNullParameterPostcomposition R D I τ).app x =
      τ.app ((dgKappaResolvedKernelContraction R D I).toDGFunctor.obj x.val) := rfl

/-- 元の厳密商延長の後合成等号の下で、同じ全次数前合成作用を回収する。 -/
theorem dgKappaNullParameterPostcomposition_heq :
    HEq (dgKappaNullParameterPostcomposition R D I τ)
      (DGQuotient.parameterPrecomposition R
        (DGQuotient.extension R (dgKappaResolvedKernelContraction R D I)) τ) :=
  DGQuotient.parameterExtension_postcomposition_heq R
    (dgKappaResolvedKernelContraction R D I) τ

end SerrePositivity.KST.NonConnective
