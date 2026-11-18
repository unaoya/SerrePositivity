module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraConvolutionConstantComparison
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraRelativeMultiplicativeSimplices
public import SerrePositivity.HomologicalAlgebra.SimplicialChains.AlexanderWhitney.SimplexCounitContraction

/-!
概要：実 AW 単体への代数の定数射の擬同型性と零単体の同型性。
方針：E2 の元の余単位の収縮を内部 Hom の前合成へ適用する。
規約：各標準単体・元の代数射を保持し、frame 条件を仮定しない。
使われ方：乗法的単体模型のホモトピー定数性と零次条件。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory HomologicalComplex
open scoped ComonObj Simplicial
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
variable (R : Type u) [CommRing R]

lemma simplexConstant_quasiIso (n : SimplexCategory) (B : Mon (Complex R)) :
    QuasiIso (convolutionConstantMap R (simplexComonoid R n) B).hom := by
  change QuasiIso (convolutionConstantHom R (simplexComonoid R n) B)
  rw [convolutionConstantHom_unit_pre, convolutionPre_eq_homPrecompose]
  have h := (_root_.SerrePositivity.HomHomotopy.homPrecomposeHomotopyEquiv
    (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cochainCounitStdSimplexHomotopyEquiv R n) B.X).quasiIso_hom
  change QuasiIso (homPrecompose ε[(simplexComonoid R n).X] B.X) at h
  infer_instance

lemma simplexConstant_zero_isIso (B : Mon (Complex R)) :
    IsIso (convolutionConstantMap R (simplexComonoid R ⦋0⦌) B) := by
  have hi : IsIso ε[(simplexComonoid R ⦋0⦌).X] :=
    _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cochainCounit_stdSimplexZero_isIso R
  have hp : IsIso ((MonoidalClosed.pre ε[(simplexComonoid R ⦋0⦌).X]).app B.X) := by
    change IsIso (((MonoidalClosed.internalHom (C := Complex R)).map
      ε[(simplexComonoid R ⦋0⦌).X].op).app B.X)
    infer_instance
  have hf : IsIso ((Mon.forget (Complex R)).map
      (convolutionConstantMap R (simplexComonoid R ⦋0⦌) B)) := by
    change IsIso (convolutionConstantHom R (simplexComonoid R ⦋0⦌) B)
    rw [convolutionConstantHom_unit_pre]
    infer_instance
  exact isIso_of_reflects_iso _ (Mon.forget (Complex R))

lemma multiplicativeSimplicesMap_quasiIso (B : Mon (Complex R))
    {m n : SimplexCategoryᵒᵖ} (f : m ⟶ n) :
    QuasiIso (((multiplicativeSimplices R B).map f).hom) := by
  have hm := simplexConstant_quasiIso R m.unop B
  have hn := simplexConstant_quasiIso R n.unop B
  have he := convolutionConstantMap_precompose R
    ((_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.simplexCochainComonFunctor R).map f.unop) B
  have hc : QuasiIso ((convolutionConstantMap R (simplexComonoid R m.unop) B).hom ≫
      ((multiplicativeSimplices R B).map f).hom) := by
    change QuasiIso (convolutionConstantMap R (simplexComonoid R m.unop) B ≫
      convolutionPrecompose R
        ((_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.simplexCochainComonFunctor R).map f.unop) B).hom
    rw [he]
    exact hn
  exact quasiIso_of_comp_left (convolutionConstantMap R (simplexComonoid R m.unop) B).hom _

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
