module

public import SerrePositivity.DifferentialGraded.Algebras.FrameFactorization
public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.ModelBifibrantLocalization
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.RightFrameHammockFamily

/-!
概要：実 dg 代数モデルへ一般 frame と bifibrant 局所化普遍性を実体化する。
方針：同じ自由 I/J の小対象論法による分解と同じ Reedy 解像を代入する。
規約：モデルを局所選択し、追加の分解仮定と SSet モデルを残さない。
使われ方：Sp の擬同型 ∞ 局所化の全写像空間比較への実入力。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.DGAlgebra
open _root_.CategoryTheory _root_.HomotopicalAlgebra
open _root_.SerrePositivity.DifferentialGraded _root_.SerrePositivity.Reedy
open _root_.SerrePositivity.InfinityCategories _root_.SerrePositivity.SimplicialModel
open _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization
variable (R : Type u) [CommRing R]

/-- 概要：実 dg モデルの source frame の全対象・全射の族。
方針：自由 I の実小対象論法による分解を Reedy 解像へ渡す。
規約：係数環以外の追加入力なし。使われ方：全 bifibrant 判定。 -/
def sourceFrameFamily :
    letI _modelInst := _root_.SerrePositivity.DGAlgebra.modelCategory R
    CofibrantResolutionFamily (C := Mon (Complex R)) simplex := by
  letI _modelInst := _root_.SerrePositivity.DGAlgebra.modelCategory R
  exact cosimplicialResolutionFamily (_root_.SerrePositivity.DGAlgebra.cofibrantFactorization R)

/-- 概要：実 dg モデルの指定 right frame の全族。
方針：自由 J の実関手的分解を反対圏の同じ Reedy 解像へ渡す。
規約：追加の分解存在入力なし。使われ方：Sp へ渡す実 Hom 単体集合。 -/
def rightFrameFamily :
    letI _modelInst := _root_.SerrePositivity.DGAlgebra.modelCategory R
    CofibrantResolutionFamily (C := (Mon (Complex R))ᵒᵖ) simplex := by
  letI _modelInst := _root_.SerrePositivity.DGAlgebra.modelCategory R
  exact _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightFrameFamilyOfFactorization (_root_.SerrePositivity.DGAlgebra.fibrantFactorization R)

/-- 概要：実 dg 代数の bifibrant hammock は擬同型による ∞ 局所化。
方針：第一分解を実自由 I の小対象論法から放電し、同じ right frame を代入する。
規約：モデル・分解・余終性の追加入力なし。
使われ方：cofibrant 部分圏と全 dg 代数への源移送の出発点。 -/
lemma bifibrantHammock_isLocalization :
    letI _modelInst := _root_.SerrePositivity.DGAlgebra.modelCategory R
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.IsLocalization
      (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.hammockLocalizationNerveMap (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantRelativeCategory (Mon (Complex R))))
      (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.weakNerveEdges (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantRelativeCategory (Mon (Complex R)))) := by
  letI _modelInst := _root_.SerrePositivity.DGAlgebra.modelCategory R
  have := _root_.SerrePositivity.DGAlgebra.modelCategory_hasFunctorialFactorization_cofibration_trivialFibration R
  exact _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.modelBifibrantHammock_isLocalization (_root_.SerrePositivity.DGAlgebra.rightFrameFamily R)

/-- 概要：実 dg right Hom と元の hammock Hom は全標的で反転後に自然同型。
方針：実 source frame・実 right frame・実第一分解を全族比較へ代入する。
規約：元の cofibrant 源だけを要求し、モデル等の追加仮定を残さない。
使われ方：Sp の全 coherent 局所化比較の同じ実入力。 -/
def rightFrameHammockFamilyIso (X : Mon (Complex R)) :
    letI _modelInst := _root_.SerrePositivity.DGAlgebra.modelCategory R
    IsCofibrant X →
      (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightFrameHom (_root_.SerrePositivity.DGAlgebra.rightFrameFamily R) X ⋙
        SSet.uliftFunctor.{u + 1, u} ⋙ AnodyneHomotopy.anodyneQ ≅
      _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.hammockHomFamily (weakEquivalences (Mon (Complex R))) X ⋙
        AnodyneHomotopy.anodyneQ) := by
  letI _modelInst := _root_.SerrePositivity.DGAlgebra.modelCategory R
  intro hX
  letI sourceCofibrant := hX
  exact _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.rightFrameHammockFamilyIso ((_root_.SerrePositivity.DGAlgebra.sourceFrameFamily R).atObject X)
    (_root_.SerrePositivity.DGAlgebra.rightFrameFamily R) (_root_.SerrePositivity.DGAlgebra.cofibrantFactorization R)

end SerrePositivity.DGAlgebra
