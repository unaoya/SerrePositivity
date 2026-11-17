module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.Adjunction
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.InvertibleEdgeLifting

/-!
概要：指定された∞随伴の単位・余単位の全関手準圏内の辺を選ぶ。
方針：h Fun の各射の辺による表示の全射性を使い、同じ射の表示であることを保持する。
規約：高次の随伴を構成済みとはしない。辺の代表は元の指定二胞体に一致する類を持つ。
使われ方：HA Proposition 4.7.3.3 の誘導モナドの構成に用いる始めのデータ。
Riehl–Verity Theorems 4.3.9・4.3.11、Kerodon Remark 6.2.1.4（Tag 02EN）。
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory MonoidalClosed SSet
open SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors
open AdjointFunctorsBetweenInfinityCategories
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories
open IsomorphismsAndIsofibrations

namespace SerrePositivity.InfinityCategories.HA.Monads

variable {C E : SSet.{u}} [Quasicategory C] [Quasicategory E]
  {F : C ⟶ E} {U : E ⟶ C}

/-- 概要：指定単位の、全自己関手準圏内の実際の辺の代表。
方針：同じh Funの射の辺による表示を選ぶ。
規約：恒等自己関手から同じF≫Uへ向く。
使われ方：HA Proposition 4.7.3.3 の指定単位の回収。 -/
def adjunctionUnitRepresentative (a : QCatAdjunction F U) :
    ((ihom C).obj C).Edge (functorVertex (𝟙 C)) (functorVertex (F ≫ U)) :=
  SSet.Edge.ofTruncated (Classical.choose
    (homotopyCategory_homMk_surjective _ _ a.unitHom))

/-- 概要：選んだ全単位の辺の類は元の指定単位である。
方針：代表を選んだ際の等式。規約：hC上の自然変換への忘却はしない。
使われ方：HA Proposition 4.7.3.3 の同じ全単位の比較。 -/
lemma adjunctionUnitRepresentative_homMk (a : QCatAdjunction F U) :
    SSet.Truncated.HomotopyCategory.homMk (adjunctionUnitRepresentative a).toTruncated =
      a.unitHom :=
  Classical.choose_spec (homotopyCategory_homMk_surjective _ _ a.unitHom)

/-- 概要：指定余単位の、全自己関手準圏内の実際の辺の代表。
方針：同じh Funの射の辺による表示を選ぶ。
規約：同じU≫Fから恒等自己関手へ向く。
使われ方：HA Proposition 4.7.3.3 の元の余単位からの積の構成。 -/
def adjunctionCounitRepresentative (a : QCatAdjunction F U) :
    ((ihom E).obj E).Edge (functorVertex (U ≫ F)) (functorVertex (𝟙 E)) :=
  SSet.Edge.ofTruncated (Classical.choose
    (homotopyCategory_homMk_surjective _ _ a.counitHom))

/-- 概要：選んだ全余単位の辺の類は元の指定余単位である。
方針：代表の選択条件。規約：元のh Fun内の二胞体として比較する。
使われ方：HA Proposition 4.7.3.3 の同じ余単位からの構成の検収。 -/
lemma adjunctionCounitRepresentative_homMk (a : QCatAdjunction F U) :
    SSet.Truncated.HomotopyCategory.homMk (adjunctionCounitRepresentative a).toTruncated =
      a.counitHom :=
  Classical.choose_spec (homotopyCategory_homMk_surjective _ _ a.counitHom)

end SerrePositivity.InfinityCategories.HA.Monads
