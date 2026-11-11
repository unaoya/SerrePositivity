module

public import SerrePositivity.EInfinity.DGAlgebra.FrameFactorization
public import SerrePositivity.EInfinity.SimplicialLocalization.ModelBifibrantLocalization
public import SerrePositivity.EInfinity.FrameHom.RightFrameHammockFamily

/-!
概要：実 dg 代数モデルへ一般 frame と bifibrant 局所化普遍性を実体化する。
方針：同じ自由 I/J の小対象論法による分解と同じ Reedy 解像を代入する。
規約：モデルを局所選択し、追加の分解仮定と SSet モデルを残さない。
使われ方：Sp の擬同型 ∞ 局所化の全写像空間比較への実入力。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.EInfinity.DGAlgebra
open CategoryTheory HomotopicalAlgebra
open SerrePositivity.DifferentialGraded SerrePositivity.Reedy
open SerrePositivity.InfinityCategories SerrePositivity.SimplicialModel
open SimplicialLocalization
variable (R : Type u) [CommRing R]

/-- 概要：実 dg モデルの source frame の全対象・全射の族。
方針：自由 I の実小対象論法による分解を Reedy 解像へ渡す。
規約：係数環以外の追加入力なし。使われ方：全 bifibrant 判定。 -/
def sourceFrameFamily :
    letI _modelInst := modelCategory R
    CofibrantResolutionFamily (C := Mon (Complex R)) simplex := by
  letI _modelInst := modelCategory R
  exact cosimplicialResolutionFamily (cofibrantFactorization R)

/-- 概要：実 dg モデルの指定 right frame の全族。
方針：自由 J の実関手的分解を反対圏の同じ Reedy 解像へ渡す。
規約：追加の分解存在入力なし。使われ方：Sp へ渡す実 Hom 単体集合。 -/
def rightFrameFamily :
    letI _modelInst := modelCategory R
    CofibrantResolutionFamily (C := (Mon (Complex R))ᵒᵖ) simplex := by
  letI _modelInst := modelCategory R
  exact _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightFrameFamilyOfFactorization (fibrantFactorization R)

/-- 概要：実 dg 代数の bifibrant hammock は擬同型による ∞ 局所化。
方針：第一分解を実自由 I の小対象論法から放電し、同じ right frame を代入する。
規約：モデル・分解・余終性の追加入力なし。
使われ方：cofibrant 部分圏と全 dg 代数への源移送の出発点。 -/
lemma bifibrantHammock_isLocalization :
    letI _modelInst := modelCategory R
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.IsLocalization
      (hammockLocalizationNerveMap (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantRelativeCategory (Mon (Complex R))))
      (weakNerveEdges (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelBifibrantRelativeCategory (Mon (Complex R)))) := by
  letI _modelInst := modelCategory R
  have := modelCategory_hasFunctorialFactorization_cofibration_trivialFibration R
  exact modelBifibrantHammock_isLocalization (rightFrameFamily R)

/-- 概要：実 dg right Hom と元の hammock Hom は全標的で反転後に自然同型。
方針：実 source frame・実 right frame・実第一分解を全族比較へ代入する。
規約：元の cofibrant 源だけを要求し、モデル等の追加仮定を残さない。
使われ方：Sp の全 coherent 局所化比較の同じ実入力。 -/
def rightFrameHammockFamilyIso (X : Mon (Complex R)) :
    letI _modelInst := modelCategory R
    IsCofibrant X →
      (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightFrameHom (rightFrameFamily R) X ⋙
        SSet.uliftFunctor.{u + 1, u} ⋙ AnodyneHomotopy.anodyneQ ≅
      FrameHom.hammockHomFamily (weakEquivalences (Mon (Complex R))) X ⋙
        AnodyneHomotopy.anodyneQ) := by
  letI _modelInst := modelCategory R
  intro hX
  letI sourceCofibrant := hX
  exact FrameHom.rightFrameHammockFamilyIso ((sourceFrameFamily R).atObject X)
    (rightFrameFamily R) (cofibrantFactorization R)

end SerrePositivity.EInfinity.DGAlgebra
