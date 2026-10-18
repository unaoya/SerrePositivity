module

public import SerrePositivity.KST.Comparison.ConstantCoefficientMaps

/-!
# horn 包含の全局所係数ホモロジー同型

概要：正次元の horn 包含は標準単体上の全ての局所係数でホモロジー同型を誘導する。
方針：初対象からの局所係数の自明化を使い、任意の定数係数の鎖ホモトピー同値へ帰着する。
規約：Weibel K-book IV.1.6。整数係数の主張から局所係数の主張を推測しない。
使われ方：基底上の horn 添付と plus の局所係数の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.Comparison
open CategoryTheory AlgebraicTopology
open scoped Simplicial

/--
概要：局所係数系の同型は誘導鎖写像の射の圏の同型を与える。
方針：源では係数同型を引き戻し、標的では元の同型を使い、自然性を適用する。
規約：同じ標的単体集合上の局所係数系。
使われ方：自明化による誘導鎖写像の擬同型性の移送。
-/
def localCoefficientChainsMapArrowIso {X Y : SSet.{u}} (f : X ⟶ Y)
    {L K : LocalCoefficientSystem Y} (e : L.coefficients ≅ K.coefficients) :
    Arrow.mk (localCoefficientChainsMap f L) ≅ Arrow.mk (localCoefficientChainsMap f K) :=
  Arrow.isoMk
    (localCoefficientChainsIso (L := pullbackLocalCoefficients f L)
      (K := pullbackLocalCoefficients f K) (Functor.isoWhiskerLeft f.mapElements e))
    (localCoefficientChainsIso e)
    (localCoefficientChainsMap_naturality f L K e.hom)

/--
概要：horn 包含は全ての標的局所係数に対する正規化鎖写像の擬同型を誘導する。
方針：標準単体の局所係数を定数係数へ自明化し、実際の定数係数鎖ホモトピー同値を使う。
規約：全ての正次元 horn。係数の平坦性を要求しない。
使われ方：局所係数ホモロジーの生成射の計算。
-/
theorem localCoefficientHorn_quasiIso {d : ℕ} [NeZero d] (k : Fin (d + 1))
    (L : LocalCoefficientSystem (Δ[d] : SSet.{u})) :
    QuasiIso (localCoefficientChainsMap (Λ[d, k]).ι L) := by
  let G := L.coefficients.obj (standardSimplexIdentityElement d)
  let K := constantLocalCoefficients (Δ[d] : SSet.{u}) G
  let e : K.coefficients ≅ L.coefficients := standardSimplexLocalCoefficientTrivialization d L
  have hk : QuasiIso (localCoefficientChainsMap (Λ[d, k]).ι K) :=
    (localConstantCoefficientMap_quasiIso_iff (Λ[d, k]).ι G).mpr
      (constantCoefficientHorn_quasiIso G k)
  exact (quasiIso_iff_of_arrow_mk_iso _ _
    (localCoefficientChainsMapArrowIso (Λ[d, k]).ι e)).mp hk

/--
概要：正次元 horn 包含は全局所係数のホモロジー同型を誘導する。
方針：構成した正規化鎖写像の擬同型性を全次数のホモロジーで評価する。
規約：標的の任意のアーベル群値局所係数系を含む。
使われ方：anodyne map の局所係数の保存へ拡張する生成射。
-/
theorem horn_localHomologyIsomorphism {d : ℕ} [NeZero d] (k : Fin (d + 1)) :
    LocalHomologyIsomorphism (Λ[d, k] : (Δ[d] : SSet.{u}).Subcomplex).ι := by
  intro L n
  have : QuasiIso (localCoefficientChainsMap (Λ[d, k]).ι L) := localCoefficientHorn_quasiIso k L
  exact (quasiIsoAt_iff_isIso_homologyMap _ n).mp inferInstance

end SerrePositivity.KST.Comparison
