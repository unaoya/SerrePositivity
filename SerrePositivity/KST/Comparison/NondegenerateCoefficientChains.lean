module

public import SerrePositivity.KST.Comparison.ConstantCoefficientMaps
public import Mathlib.AlgebraicTopology.SimplicialSet.Homology.Nondegenerate
public import Mathlib.AlgebraicTopology.DoldKan.Normalized

/-!
# 非退化単体による係数複体と Moore 正規化の比較

概要：非退化単体の直和の複体を実際の Moore 正規化複体と同型で結ぶ。
方針：Dold–Kan の共通の Karoubi 包絡での同型を充満忠実性で戻す。
規約：Weibel K-book IV.1.5 のセル添付の計算。鎖ホモトピー同値だけでなく同型を使う。
使われ方：セルの相対複体の支持次数と境界写像の計算。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.Comparison
open CategoryTheory CategoryTheory.Idempotents AlgebraicTopology
open scoped Simplicial

/--
概要：非退化単体の係数複体と Moore 正規化複体の実際の同型。
方針：二つの複体を P∞ の像として Karoubi 包絡で同定し、その同型を戻す。
規約：任意のアーベル群係数。
使われ方：標準セルの係数複体の計算。
-/
def nondegenerateCoefficientChainsIso (X : SSet.{u}) (G : AddCommGrpCat.{u}) :
    X.normalizedChainComplex G ≅
      (normalizedMooreComplex _).obj ((constantCoefficientSimplicialFunctor G).obj X) :=
  (toKaroubi _).preimageIso
    ((X.splitting.map (CategoryTheory.Limits.sigmaConst.obj G)).toKaroubiNondegComplexIsoN₁ ≪≫
      (DoldKan.N₁_iso_normalizedMooreComplex_comp_toKaroubi AddCommGrpCat.{u}).app _)

/--
概要：非退化複体への比較の逆射は Moore 包含と非退化射影の合成である。
方針：Karoubi 包絡の同型の式と P∞ の包含への作用を使う。
規約：実際の鎖写像の等式。
使われ方：比較の自然性。
-/
theorem nondegenerateCoefficientChainsIso_inv (X : SSet.{u}) (G : AddCommGrpCat.{u}) :
    (nondegenerateCoefficientChainsIso X G).inv =
      inclusionOfMooreComplexMap ((constantCoefficientSimplicialFunctor G).obj X) ≫
        X.toNormalizedChainComplex G := by
  apply (toKaroubi _).map_injective
  simp only [nondegenerateCoefficientChainsIso, Functor.preimageIso_inv, Functor.map_preimage]
  apply Karoubi.hom_ext
  dsimp [DoldKan.N₁_iso_normalizedMooreComplex_comp_toKaroubi,
    SSet.toNormalizedChainComplex]
  have ht : (X.splitting.map (CategoryTheory.Limits.sigmaConst.obj G)).toNondegComplex =
      DoldKan.PInfty ≫
        (X.splitting.map
          (CategoryTheory.Limits.sigmaConst.obj G)).toKaroubiNondegComplexIsoN₁.inv.f := by
    apply HomologicalComplex.hom_ext
    intro n
    exact (X.splitting.map (CategoryTheory.Limits.sigmaConst.obj G)).toNondegComplex_f n
  rw [ht, ← Category.assoc, DoldKan.inclusionOfMooreComplexMap_comp_PInfty]
  rfl

/--
概要：非退化複体との比較の逆射は単体写像に関して自然である。
方針：Moore 包含の自然性と非退化射影の自然性を合成する。
規約：任意の定数係数群。
使われ方：相対複体へ同型を移す。
-/
theorem nondegenerateCoefficientChainsIso_inv_naturality {X Y : SSet.{u}}
    (f : X ⟶ Y) (G : AddCommGrpCat.{u}) :
    (normalizedMooreComplex _).map ((constantCoefficientSimplicialFunctor G).map f) ≫
        (nondegenerateCoefficientChainsIso Y G).inv =
      (nondegenerateCoefficientChainsIso X G).inv ≫ SSet.normalizedChainComplexMap f G := by
  rw [nondegenerateCoefficientChainsIso_inv, nondegenerateCoefficientChainsIso_inv]
  have hn : (normalizedMooreComplex _).map ((constantCoefficientSimplicialFunctor G).map f) ≫
      inclusionOfMooreComplexMap ((constantCoefficientSimplicialFunctor G).obj Y) =
    inclusionOfMooreComplexMap ((constantCoefficientSimplicialFunctor G).obj X) ≫
      SSet.chainComplexMap f G :=
    (inclusionOfMooreComplex AddCommGrpCat.{u}).naturality _
  rw [← Category.assoc, hn, Category.assoc,
    ← SSet.toNormalizedChainComplex_normalizedChainComplexMap, Category.assoc]

/--
概要：定数局所係数の複体と非退化単体の直和の複体の同型。
方針：定数係数の Kan 拡張比較と Moore 正規化との同型を合成する。
規約：実際の鎖複体の同型。
使われ方：局所係数の自明化後のセル計算。
-/
def constantLocalCoefficientNondegenerateIso (X : SSet.{u}) (G : AddCommGrpCat.{u}) :
    localCoefficientChains X (constantLocalCoefficients X G) ≅ X.normalizedChainComplex G :=
  constantLocalCoefficientChainsIso X G ≪≫ (nondegenerateCoefficientChainsIso X G).symm

end SerrePositivity.KST.Comparison
