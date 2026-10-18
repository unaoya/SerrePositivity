module

public import SerrePositivity.KST.DerivedBlowup.ExteriorBaseChangeDegreeDifferential
public import SerrePositivity.HomologicalAlgebra.BaseChange

/-!
概要：KST Def3.1 の Koszul 外積 chain 複体のスカラー拡大同型。
方針：次数別外積の底変更同型を微分適合性で複体同型へまとめる。
規約：環準同型により係数環の代数構造を固定する。
使われ方：Koszul dg 代数の underlying 複体の底変更比較。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.KST.DerivedBlowup

open CategoryTheory
open scoped TensorProduct

variable {R S M : Type u} [CommRing R] [CommRing S] [AddCommGroup M] [Module R M]

/-- 概要：Koszul 外積 chain 複体は環準同型によるスカラー拡大と可換。
方針：各次数の外積基底変更同型と次数別収縮の比較を使う。
規約：KST Def3.1、平坦性と2の可逆性は不要。
使われ方：整数 cochain への零延長後の底変更比較。 -/
def exteriorChainBaseChangeIso (φ : R →+* S) (d : M →ₗ[R] R) :
    letI := φ.toAlgebra
    exteriorKoszulChain (exteriorBaseChangeDifferential (S := S) d) ≅
      ((ModuleCat.extendScalars φ).mapHomologicalComplex (ComplexShape.down ℕ)).obj
        (exteriorKoszulChain d) := by
  letI := φ.toAlgebra
  refine HomologicalComplex.Hom.isoOfComponents
    (fun n => (exteriorDegreeBaseChangeEquiv (R := R) (S := S) (M := M) n).toModuleIso) ?_
  intro i j hij
  obtain rfl : i = j + 1 := hij.symm
  simp only [Functor.mapHomologicalComplex_obj_d, exteriorKoszulChain, ChainComplex.of_d]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  change TensorProduct.AlgebraTensorModule.map (LinearMap.id : S →ₗ[S] S)
      (exteriorDegreeDifferential d j) (exteriorDegreeToBaseChange (j + 1) z) =
    exteriorDegreeToBaseChange j
      (exteriorDegreeDifferential (exteriorBaseChangeDifferential d) j z)
  exact (exteriorDegreeToBaseChange_d d j z).symm

end SerrePositivity.KST.DerivedBlowup
