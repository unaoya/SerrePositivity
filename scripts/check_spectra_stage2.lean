-- lake build SerrePositivity.Spectra.StageTwo の後に実行する。
-- 段階2の入口で公開する API を、一般の単体的豊穣構造と作用の比較を使って検証する。
import SerrePositivity.Spectra.StageTwo
import SerrePositivity.CategoryTheory.Enriched.Simplicial
import SerrePositivity.CategoryTheory.Monoidal.Action

universe u

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.MonoidalClosed
open SerrePositivity SerrePositivity.SymmetricSpectrum
open SerrePositivity.GeneralSymmetricSpectrum (level suspensionMap adjointStructureMap
  adjointStructureMap_naturality pointwiseTensorAssociator
  pointwiseTensorAssociator_level pointwiseTensorAssociator_parameter_naturality
  pointwiseTensorUnitIso pointwiseTensorUnitIso_level
  pointwiseTensorPentagonLaw pointwiseTensor_pentagon pointwiseTensorTriangleLaw
  pointwiseTensor_triangle pointwiseTensorLeftUnitLaw pointwiseTensor_left_unit)
open SerrePositivity.PointedSimplicialSet
  (adjoinBasepointFunctor adjoinBasepointProductIso adjoinBasepointProductIso_inv_naturality)
open scoped Simplicial

-- 基点付きの作用の随伴、各段の比較、単位・結合の整合性。
example (X : PointedSimplicialSet.{u}) : pointwiseTensorFunctor X ⊣ cotensorFunctor X :=
  pointwiseTensorCotensorAdjunction X

example (E : SymmetricSpectrum.{u}) (q : ℕ) :
    (pointwiseTensorUnitIso E).hom.hom.app (FiniteBijection.of q) =
      (λ_ (level E q)).hom := pointwiseTensorUnitIso_level E q

example (X Y : PointedSimplicialSet.{u}) (E : SymmetricSpectrum.{u}) (q : ℕ) :
    (pointwiseTensorAssociator X Y E).hom.hom.app (FiniteBijection.of q) =
      (α_ X Y (level E q)).hom := pointwiseTensorAssociator_level X Y E q

example (X Y Z : PointedSimplicialSet.{u}) (E : SymmetricSpectrum.{u}) :
    pointwiseTensorPentagonLaw X Y Z E := pointwiseTensor_pentagon X Y Z E

example (X : PointedSimplicialSet.{u}) (E : SymmetricSpectrum.{u}) :
    pointwiseTensorTriangleLaw X E := pointwiseTensor_triangle X E

example (X : PointedSimplicialSet.{u}) (E : SymmetricSpectrum.{u}) :
    pointwiseTensorLeftUnitLaw X E := pointwiseTensor_left_unit X E

-- 基点付きの豊穣構造を忘却関手で移送し、標準の射と零次単体を照合する。
section

local instance : EnrichedOrdinaryCategory PointedSimplicialSet.{u} SymmetricSpectrum.{u} :=
  pointedMappingEnrichedOrdinaryCategory

local instance : SimplicialCategory SymmetricSpectrum.{u} :=
  TransportOrdinaryEnrichment.ordinaryCategory PointedSimplicialSet.forget.{u}
    SymmetricSpectrum.{u} PointedSimplicialSet.forgetUnitHomEquiv.{u}
    PointedSimplicialSet.forgetUnitHomEquiv_formula.{u}

example (E F : SymmetricSpectrum.{u}) :
    SimplicialCategory.homEquiv' E F = simplicialMappingVertexEquiv E F :=
  mappingSpaceSimplicialCategory_vertexEquiv E F

example (E : SymmetricSpectrum.{u}) : SimplicialHomLaws.identityLaw E :=
  SimplicialHomLaws.identity E

example {E F G : SymmetricSpectrum.{u}} (f : E ⟶ F) (g : F ⟶ G) :
    SimplicialHomLaws.compositionLaw f g := SimplicialHomLaws.composition f g

end

-- 写像対象を経由した転置は、余テンソルへの転置と一致する。
example (K : SSet.{u}) (E F : SymmetricSpectrum.{u}) (f : simplicialTensor K E ⟶ F) :
    (((simplicialTensorMappingAdjunction E).homEquiv K F).symm.trans
      ((simplicialTensorCotensorAdjunction K).homEquiv E F))
      ((simplicialTensorMappingAdjunction E).homEquiv K F f) =
        (simplicialTensorCotensorAdjunction K).homEquiv E F f := by
  rw [Equiv.trans_apply, Equiv.symm_apply_apply]
  rfl

-- Δ[0]はtensor・cotensorの両方の単位。
example (E : SymmetricSpectrum.{u}) : simplicialTensor (Δ[0] : SSet.{u}) E ≅ E :=
  simplicialTensorUnitNatIso.app E

example (E : SymmetricSpectrum.{u}) : simplicialCotensor (Δ[0] : SSet.{u}) E ≅ E :=
  (ActionUnitAdjunction.rightUnitIso
    (simplicialTensorCotensorAdjunction (Δ[0] : SSet.{u})) simplicialTensorUnitNatIso).app E

-- 直積による反復比較と、そのパラメータ自然性。
example (K L : SSet.{u}) (E : SymmetricSpectrum.{u}) :
    simplicialTensor (K ⊗ L) E ≅ simplicialTensor K (simplicialTensor L E) :=
  (simplicialTensorProductNatIso K L).app E

example (K L : SSet.{u}) (E : SymmetricSpectrum.{u}) :
    simplicialCotensor (K ⊗ L) E ≅ simplicialCotensor L (simplicialCotensor K E) :=
  (ActionComparisonAdjunction.rightIso (simplicialTensorCotensorAdjunction (K ⊗ L))
    ((simplicialTensorCotensorAdjunction L).comp (simplicialTensorCotensorAdjunction K))
    (simplicialTensorProductNatIso K L)).app E

example {K K' L L' : SSet.{u}} (f : K ⟶ K') (g : L ⟶ L') (E : SymmetricSpectrum.{u}) :
    ActionProductComparison.parameterLaw adjoinBasepointFunctor.{u} pointwiseTensorBifunctor.{u}
      pointwiseTensorAssociatorNatIso.{u} adjoinBasepointProductIso.{u} f g E :=
  ActionProductComparison.parameter adjoinBasepointFunctor.{u} pointwiseTensorBifunctor.{u}
      pointwiseTensorAssociatorNatIso.{u} adjoinBasepointProductIso.{u} f g E
      (adjoinBasepointProductIso_inv_naturality f g)
      (pointwiseTensorAssociator_parameter_naturality
        (adjoinBasepointFunctor.map f) (adjoinBasepointFunctor.map g) E)

example {K K' L L' : SSet.{u}} (f : K ⟶ K') (g : L ⟶ L') (E : SymmetricSpectrum.{u}) :
    ActionComparisonNaturality.parameterLaw
      (simplicialTensorCotensorAdjunction (K ⊗ L))
      (simplicialTensorCotensorAdjunction (K' ⊗ L'))
      ((simplicialTensorCotensorAdjunction L).comp (simplicialTensorCotensorAdjunction K))
      ((simplicialTensorCotensorAdjunction L').comp (simplicialTensorCotensorAdjunction K'))
      (simplicialTensorProductNatIso K L) (simplicialTensorProductNatIso K' L')
      (fun F => simplicialCotensorPre (f ⊗ₘ g) F)
      (fun F => (simplicialCotensorFunctor L').map (simplicialCotensorPre f F) ≫
        simplicialCotensorPre g (simplicialCotensor K F)) E := by
  let cotensorAction := GeneralSymmetricSpectrum.cotensorBifunctor (K := PointedSimplicialSet.circle.{u})
  refine ActionComparisonNaturality.parameter_composite
    (simplicialTensorCotensorAdjunction L) (simplicialTensorCotensorAdjunction L')
    (simplicialTensorCotensorAdjunction K) (simplicialTensorCotensorAdjunction K')
    (pointwiseTensorBifunctor.map (adjoinBasepointFunctor.map g))
    (pointwiseTensorBifunctor.map (adjoinBasepointFunctor.map f))
    (cotensorAction.map (adjoinBasepointFunctor.map g).op)
    (cotensorAction.map (adjoinBasepointFunctor.map f).op)
    (simplicialTensorCotensorAdjunction (K ⊗ L))
    (simplicialTensorCotensorAdjunction (K' ⊗ L'))
    (simplicialTensorProductNatIso K L) (simplicialTensorProductNatIso K' L')
    (fun F => simplicialTensorPost (f ⊗ₘ g) F)
    (fun F => simplicialCotensorPre (f ⊗ₘ g) F)
    ?_ ?_ ?_ E
  · intro F G h
    exact simplicialTensorCotensorHomEquiv_post (f ⊗ₘ g) h
  · intro F G h
    exact ActionComparisonNaturality.composite_pre
      (simplicialTensorCotensorAdjunction L) (simplicialTensorCotensorAdjunction L')
      (simplicialTensorCotensorAdjunction K) (simplicialTensorCotensorAdjunction K')
      (pointwiseTensorBifunctor.map (adjoinBasepointFunctor.map g))
      (pointwiseTensorBifunctor.map (adjoinBasepointFunctor.map f))
      (cotensorAction.map (adjoinBasepointFunctor.map g).op)
      (cotensorAction.map (adjoinBasepointFunctor.map f).op)
      (fun _ _ h => simplicialTensorCotensorHomEquiv_post g h)
      (fun _ _ h => simplicialTensorCotensorHomEquiv_post f h) F G h
  · intro F
    exact ActionProductComparison.parameter adjoinBasepointFunctor.{u} pointwiseTensorBifunctor.{u}
      pointwiseTensorAssociatorNatIso.{u} adjoinBasepointProductIso.{u} f g F
      (adjoinBasepointProductIso_inv_naturality f g)
      (GeneralSymmetricSpectrum.pointwiseTensorAssociator_parameter_naturality
        (adjoinBasepointFunctor.map f) (adjoinBasepointFunctor.map g) F)

-- 円による随伴は、転置・逆転置が互いに逆となる実際の随伴。
example : suspensionFunctor.{u} ⊣
    loopFunctor.{u} := suspensionLoopAdjunction

example (E F : SymmetricSpectrum.{u}) (f : suspensionFunctor.obj E ⟶ F) :
    ((suspensionLoopAdjunction.homEquiv E F).symm
      (suspensionLoopAdjunction.homEquiv E F f)) = f :=
  (suspensionLoopAdjunction.homEquiv E F).symm_apply_apply f

example (E : SymmetricSpectrum.{u}) :
    suspensionFunctor.map (suspensionLoopAdjunction.unit.app E) ≫
      suspensionLoopAdjunction.counit.app (suspensionFunctor.obj E) =
        𝟙 (suspensionFunctor.obj E) :=
  suspensionLoopAdjunction.left_triangle_components E

example (E : SymmetricSpectrum.{u}) :
    let R := loopFunctor.{u}
    suspensionLoopAdjunction.unit.app (R.obj E) ≫
      R.map (suspensionLoopAdjunction.counit.app E) = 𝟙 (R.obj E) :=
  suspensionLoopAdjunction.right_triangle_components E

example (E : SymmetricSpectrum.{u}) (q : ℕ) :
    level (suspensionFunctor.obj E) q =
      (PointedSimplicialSet.circle : PointedSimplicialSet.{u}) ⊗ level E q :=
  GeneralSymmetricSpectrum.pointwiseTensor_level PointedSimplicialSet.circle E q

example (E : SymmetricSpectrum.{u}) (q : ℕ) :
    level (GeneralSymmetricSpectrum.cotensor PointedSimplicialSet.circle E) q =
      (ihom (PointedSimplicialSet.circle : PointedSimplicialSet.{u})).obj (level E q) :=
  GeneralSymmetricSpectrum.cotensor_level PointedSimplicialSet.circle E q

-- 構造射の転置は同じ n+1 段の射へ戻り、スペクトル射とも両立する。
example (E : SymmetricSpectrum.{u}) (n : ℕ) :
    uncurry (adjointStructureMap E n) = suspensionMap E n :=
  GeneralSymmetricSpectrum.uncurry_adjointStructureMap E n

example (E : SymmetricSpectrum.{u}) (n : ℕ) :
    curry (uncurry (adjointStructureMap E n)) = adjointStructureMap E n :=
  curry_uncurry _

example {E F : SymmetricSpectrum.{u}} (f : E ⟶ F) (n : ℕ) :
    f.hom.app (FiniteBijection.of n) ≫ adjointStructureMap F n =
      adjointStructureMap E n ≫
        (ihom (PointedSimplicialSet.circle : PointedSimplicialSet.{u})).map
          (f.hom.app (FiniteBijection.of (n + 1))) := adjointStructureMap_naturality f n
