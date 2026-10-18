module

public import SerrePositivity.KST.Comparison.ConstantCoefficientComparison
public import SerrePositivity.KST.Comparison.LocalCoefficientNaturality
public import SerrePositivity.KST.Comparison.ChainPairContraction

/-!
# 定数局所係数の誘導写像と鎖複体の擬同型

概要：定数局所係数の誘導鎖写像を、Mathlib の定数係数鎖写像と比較する。
方針：Kan 拡張の単位による自然性と、正規化の鎖ホモトピー同値を使う。
規約：Weibel K-book IV.1.6。任意のアーベル群係数。
使われ方：局所係数の horn のホモロジー同型。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.Comparison
open CategoryTheory CategoryTheory.Limits AlgebraicTopology

/--
概要：定数係数の比較写像は基底の単体写像に関して自然である。
方針：源の Kan 拡張の単位で判定し、各単体の直和包含の式を使う。
規約：任意の係数アーベル群。
使われ方：正規化鎖写像の比較。
-/
theorem constantCoefficientComparison_naturality {X Y : SSet.{u}} (f : X ⟶ Y)
    (G : AddCommGrpCat.{u}) :
    localCoefficientSimplicialMap f (constantLocalCoefficients Y G) ≫
      constantCoefficientComparison Y G =
    constantCoefficientComparison X G ≫ (constantCoefficientSimplicialFunctor G).map f := by
  apply Functor.leftKanExtension_hom_ext (Functor.Elements.π X)
    (constantLocalCoefficients X G).coefficients
  apply NatTrans.ext
  funext e
  let uX := ((Functor.Elements.π X).leftKanExtensionUnit
    (constantLocalCoefficients X G).coefficients).app e
  let uY := ((Functor.Elements.π Y).leftKanExtensionUnit
    (constantLocalCoefficients Y G).coefficients).app (f.mapElements.obj e)
  let m := (localCoefficientSimplicialMap f (constantLocalCoefficients Y G)).app e.obj
  let cX := (constantCoefficientComparison X G).app e.obj
  let cY := (constantCoefficientComparison Y G).app e.obj
  let Ff := ((constantCoefficientSimplicialFunctor G).map f).app e.obj
  have hm : uX ≫ m = uY := localCoefficientSimplicialMap_unit f _ e
  have hcX : uX ≫ cX = Sigma.ι (fun _ : X.obj e.obj => G) e.val :=
    constantCoefficientComparison_unit X G e
  have hcY : uY ≫ cY = Sigma.ι (fun _ : Y.obj e.obj => G) (f.app e.obj e.val) :=
    constantCoefficientComparison_unit Y G (f.mapElements.obj e)
  have hgen : Sigma.ι (fun _ : Y.obj e.obj => G) (f.app e.obj e.val) =
      Sigma.ι (fun _ : X.obj e.obj => G) e.val ≫ Ff := by
    change Sigma.ι (fun _ : Y.obj e.obj => G) (f.app e.obj e.val) =
      Sigma.ι (fun _ : X.obj e.obj => G) e.val ≫ Sigma.map' (f.app e.obj) (fun _ => 𝟙 G)
    rw [Sigma.ι_comp_map', Category.id_comp]
  change uX ≫ (m ≫ cY) = uX ≫ (cX ≫ Ff)
  calc
    _ = (uX ≫ m) ≫ cY := (Category.assoc _ _ _).symm
    _ = uY ≫ cY := congrArg (fun q => q ≫ cY) hm
    _ = Sigma.ι (fun _ : Y.obj e.obj => G) (f.app e.obj e.val) := hcY
    _ = Sigma.ι (fun _ : X.obj e.obj => G) e.val ≫ Ff := hgen
    _ = (uX ≫ cX) ≫ Ff := congrArg (fun q => q ≫ Ff) hcX.symm
    _ = uX ≫ (cX ≫ Ff) := Category.assoc _ _ _

/--
概要：定数局所係数の複体と直和模型の正規化複体の同型。
方針：証明済みの単体的自然同型に Moore 正規化を施す。
規約：実際の複体の同型。
使われ方：誘導写像の擬同型性の比較。
-/
def constantLocalCoefficientChainsIso (X : SSet.{u}) (G : AddCommGrpCat.{u}) :
    localCoefficientChains X (constantLocalCoefficients X G) ≅
      (normalizedMooreComplex _).obj ((constantCoefficientSimplicialFunctor G).obj X) :=
  (normalizedMooreComplex _).mapIso (constantCoefficientSimplicialIso X G)

/--
概要：定数係数の鎖複体比較は誘導鎖写像と可換である。
方針：単体的群での自然性を正規化へ渡す。
規約：任意の単体写像と係数群。
使われ方：射の圏の比較同型。
-/
theorem constantLocalCoefficientChainsIso_naturality {X Y : SSet.{u}} (f : X ⟶ Y)
    (G : AddCommGrpCat.{u}) :
    localCoefficientChainsMap f (constantLocalCoefficients Y G) ≫
      (constantLocalCoefficientChainsIso Y G).hom =
    (constantLocalCoefficientChainsIso X G).hom ≫
      (normalizedMooreComplex _).map ((constantCoefficientSimplicialFunctor G).map f) := by
  change (normalizedMooreComplex _).map
      (localCoefficientSimplicialMap f (constantLocalCoefficients Y G)) ≫
        (normalizedMooreComplex _).map (constantCoefficientComparison Y G) =
    (normalizedMooreComplex _).map (constantCoefficientComparison X G) ≫
      (normalizedMooreComplex _).map ((constantCoefficientSimplicialFunctor G).map f)
  rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
  exact congrArg (fun q => (normalizedMooreComplex AddCommGrpCat.{u}).map q)
    (constantCoefficientComparison_naturality f G)

/--
概要：単体的アーベル群の写像の正規化の擬同型性と交互面複体の擬同型性は同値である。
方針：正規化包含の自然性と鎖ホモトピー同値による二対三性を使う。
規約：任意の単体的アーベル群の射。
使われ方：Mathlib の定数係数鎖複体への比較。
-/
theorem normalizedMooreMap_quasiIso_iff
    {S T : SimplicialObject AddCommGrpCat.{u}} (f : S ⟶ T) :
    QuasiIso ((normalizedMooreComplex _).map f) ↔
      QuasiIso ((alternatingFaceMapComplex _).map f) := by
  have (V : SimplicialObject AddCommGrpCat.{u}) : QuasiIso (inclusionOfMooreComplexMap V) :=
    (DoldKan.homotopyEquivNormalizedMooreComplexAlternatingFaceMapComplex
      (Y := V)).quasiIso_hom
  have he : (normalizedMooreComplex _).map f ≫ inclusionOfMooreComplexMap T =
      inclusionOfMooreComplexMap S ≫ (alternatingFaceMapComplex _).map f :=
    (inclusionOfMooreComplex AddCommGrpCat).naturality f
  rw [← quasiIso_iff_comp_right _ (inclusionOfMooreComplexMap T), he,
    quasiIso_iff_comp_left]

/--
概要：定数局所係数の誘導鎖写像の擬同型性は Mathlib の定数係数鎖写像のものと同値である。
方針：正規化複体の比較同型で射を移し、その後正規化を除く。
規約：任意のアーベル群係数。
使われ方：定数係数の horn の局所係数としての計算。
-/
theorem localConstantCoefficientMap_quasiIso_iff {X Y : SSet.{u}} (f : X ⟶ Y)
    (G : AddCommGrpCat.{u}) :
    QuasiIso (localCoefficientChainsMap f (constantLocalCoefficients Y G)) ↔
      QuasiIso (SSet.chainComplexMap f G) := by
  let e : Arrow.mk (localCoefficientChainsMap f (constantLocalCoefficients Y G)) ≅
      Arrow.mk ((normalizedMooreComplex _).map ((constantCoefficientSimplicialFunctor G).map f)) :=
    Arrow.isoMk (constantLocalCoefficientChainsIso X G) (constantLocalCoefficientChainsIso Y G)
      (constantLocalCoefficientChainsIso_naturality f G).symm
  rw [quasiIso_iff_of_arrow_mk_iso _ _ e, normalizedMooreMap_quasiIso_iff]
  rfl

end SerrePositivity.KST.Comparison
