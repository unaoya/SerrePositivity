module

public import SerrePositivity.KST.Comparison.LocalCoefficientAnodyne
public import SerrePositivity.HomotopicalAlgebra.Simplicial.AnodyneKanReplacement

/-!
# Kan 置換と全局所係数ホモロジー

概要：実際の Kan 置換の単位は全局所係数ホモロジー同型である。
方針：構成済みの単位の anodyne 性に slice の小対象構成の帰結を適用する。
規約：Weibel K-book IV.1.6、Waldhausen LNM 1126 §1.7・§1.8。
使われ方：セル添付した plus の候補を Kan 複体へ移す。
-/

@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.Comparison
open SerrePositivity.SimplicialModel

/--
概要：Kan 置換の単位は全ての標的局所係数でホモロジー同型を誘導する。
方針：単位の実際の anodyne 性を局所係数の保存へ渡す。
規約：源の局所係数は標的からの引き戻し。
使われ方：plus の acyclic 性を Kan 置換後へ移す。
-/
theorem kanReplacementUnit_localHomologyIsomorphism (X : SSet.{u}) :
    LocalHomologyIsomorphism (AnodyneKanReplacement.unit.app X) :=
  localHomologyIsomorphism_of_anodyne _ (AnodyneKanReplacement.unit_anodyne X)

end SerrePositivity.KST.Comparison
