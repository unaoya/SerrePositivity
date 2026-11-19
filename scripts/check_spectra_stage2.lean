-- lake build SerrePositivity.Spectra.StageTwo の後に実行する。
-- 段階2の入口だけから、計画の最終確認に指定したAPIを利用できることを検証する。
import SerrePositivity.Spectra.StageTwo

universe u

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.MonoidalClosed
open SerrePositivity SerrePositivity.SymmetricSpectrum
open SerrePositivity.GeneralSymmetricSpectrum (level)
open scoped Simplicial

-- 基点付きの作用の随伴、各段の比較、単位・結合の整合性。
example (X : PointedSimplicialSet.{u}) : pointwiseTensorFunctor X ⊣ cotensorFunctor X :=
  pointwiseTensorCotensorAdjunction X

example (E : SymmetricSpectrum.{u}) (q : ℕ) :
    (pointwiseTensorUnitIso E).hom.hom.app (FiniteBijection.of q) =
      (λ_ (level E q)).hom := pointwiseTensorUnitIso_app E q

example (X Y : PointedSimplicialSet.{u}) (E : SymmetricSpectrum.{u}) (q : ℕ) :
    (pointwiseTensorAssociator X Y E).hom.hom.app (FiniteBijection.of q) =
      (α_ X Y (level E q)).hom := pointwiseTensorAssociator_level X Y E q

example (X Y Z : PointedSimplicialSet.{u}) (E : SymmetricSpectrum.{u}) :
    pointwiseTensorPentagonLaw X Y Z E := pointwiseTensor_pentagon X Y Z E

example (X : PointedSimplicialSet.{u}) (E : SymmetricSpectrum.{u}) :
    pointwiseTensorTriangleLaw X E := pointwiseTensor_triangle X E

example (X : PointedSimplicialSet.{u}) (E : SymmetricSpectrum.{u}) :
    pointwiseTensorLeftUnitLaw X E := pointwiseTensor_left_unit X E

-- 標準の単体的豊穣構造と通常の射の対応。
example (E F : SymmetricSpectrum.{u}) :
    let : SimplicialCategory SymmetricSpectrum.{u} := mappingSpaceSimplicialCategory
    SimplicialCategory.homEquiv' E F = simplicialMappingVertexEquiv E F :=
  mappingSpaceSimplicialCategory_vertexEquiv E F

-- 通常の恒等射と合成が零次単体の単位・合成に対応する。
example (E : SymmetricSpectrum.{u}) : simplicialMappingVertexIdentityLaw E :=
  simplicialMappingVertex_identity E

example {E F G : SymmetricSpectrum.{u}} (f : E ⟶ F) (g : F ⟶ G) :
    simplicialMappingVertexCompositionLaw f g := simplicialMappingVertex_composition f g

-- 三つのHom同値の二つの経路が同じ転置を与える。
example (K : SSet.{u}) (E F : SymmetricSpectrum.{u}) (f : simplicialTensor K E ⟶ F) :
    simplicialMappingCotensorHomEquiv K E F (simplicialTensorMappingHomEquiv K E F f) =
      simplicialTensorCotensorHomEquiv K E F f := simplicialHomEquiv_compatibility K E F f

-- Δ[0]はtensor・cotensorの両方の単位。
example (E : SymmetricSpectrum.{u}) : simplicialTensor (Δ[0] : SSet.{u}) E ≅ E :=
  simplicialTensorUnitIso E

example (E : SymmetricSpectrum.{u}) : simplicialCotensor (Δ[0] : SSet.{u}) E ≅ E :=
  simplicialCotensorUnitIso E

-- 直積による反復比較と、そのパラメータ自然性。
example (K L : SSet.{u}) (E : SymmetricSpectrum.{u}) :
    simplicialTensor (K ⊗ L) E ≅ simplicialTensor K (simplicialTensor L E) :=
  simplicialTensorProductIso K L E

example (K L : SSet.{u}) (E : SymmetricSpectrum.{u}) :
    simplicialCotensor (K ⊗ L) E ≅ simplicialCotensor L (simplicialCotensor K E) :=
  simplicialCotensorProductIso K L E

example {K K' L L' : SSet.{u}} (f : K ⟶ K') (g : L ⟶ L') (E : SymmetricSpectrum.{u}) :
    simplicialTensorProductParameterLaw f g E := simplicialTensorProduct_parameter f g E

example {K K' L L' : SSet.{u}} (f : K ⟶ K') (g : L ⟶ L') (E : SymmetricSpectrum.{u}) :
    simplicialCotensorProductParameterLaw f g E := simplicialCotensorProduct_parameter f g E

-- 円による随伴は、転置・逆転置が互いに逆となる実際の随伴。
example : suspensionFunctor.{u} ⊣ loopFunctor.{u} := suspensionLoopAdjunction

example (E F : SymmetricSpectrum.{u}) (f : suspension E ⟶ F) :
    (suspensionLoopHomEquiv E F).symm (suspensionLoopHomEquiv E F f) = f :=
  (suspensionLoopHomEquiv E F).symm_apply_apply f

example (E : SymmetricSpectrum.{u}) :
    suspensionFunctor.map (suspensionLoopUnit E) ≫ suspensionLoopCounit (suspension E) =
      𝟙 (suspension E) := suspensionLoop_left_triangle E

example (E : SymmetricSpectrum.{u}) :
    suspensionLoopUnit (loops E) ≫ loopFunctor.map (suspensionLoopCounit E) = 𝟙 (loops E) :=
  suspensionLoop_right_triangle E

example (E : SymmetricSpectrum.{u}) (q : ℕ) :
    level (suspension E) q = (PointedSimplicialSet.circle : PointedSimplicialSet.{u}) ⊗ level E q :=
  suspension_level E q

example (E : SymmetricSpectrum.{u}) (q : ℕ) :
    level (loops E) q =
      (ihom (PointedSimplicialSet.circle : PointedSimplicialSet.{u})).obj (level E q) :=
  loops_level E q

-- 構造射の転置は同じ n+1 段の射へ戻り、スペクトル射とも両立する。
example (E : SymmetricSpectrum.{u}) (n : ℕ) :
    uncurry (adjointStructureMap E n) = suspensionMap E n := uncurry_adjointStructureMap E n

example (E : SymmetricSpectrum.{u}) (n : ℕ) :
    curry (uncurry (adjointStructureMap E n)) = adjointStructureMap E n :=
  curry_uncurry_adjointStructureMap E n

example {E F : SymmetricSpectrum.{u}} (f : E ⟶ F) (n : ℕ) :
    f.hom.app (FiniteBijection.of n) ≫ adjointStructureMap F n =
      adjointStructureMap E n ≫
        (ihom (PointedSimplicialSet.circle : PointedSimplicialSet.{u})).map
          (f.hom.app (FiniteBijection.of (n + 1))) := adjointStructureMap_naturality f n
