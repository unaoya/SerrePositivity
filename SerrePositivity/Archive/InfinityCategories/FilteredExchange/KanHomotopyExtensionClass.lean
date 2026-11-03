module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.HomotopyIsoWhiskering
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentTotalVertexPath

/-!
概要：元の単位上の指定 path 類が一致すれば Kan 延長後の指定同型も一致する。
方針：全円柱の制限式を両端の自然性で輸送し、単位の前合成の忠実性で反映する。
規約：任意の指定延長に対する等式。使われ方：底固定円柱と既存の native 比較候補の接続。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {A X : SSet.{u}} {f g : A ⟶ X}

/-- 概要：指定 Kan 延長の単位による前合成は元の円柱の単位像の指定同型。
方針：同じ全円柱の端点輸送と前合成の辺の類。
規約：元の指定延長を保持。使われ方：単位上の指定類の反映。 -/
lemma kanHomotopyExtension_precomp_iso (H : SSet.Homotopy f g)
    (L : SSet.Homotopy (continuousKanReplacement.map f) (continuousKanReplacement.map g))
    (hL : (continuousKanReplacementUnit.app A ▷ (Δ[1] : SSet.{u})) ≫ L.h =
      H.h ≫ continuousKanReplacementUnit.app X) :
    (functorIsoOfSimplicialHomotopy L).precomp (continuousKanReplacementUnit.app A) =
      functorIsoOfEq
        (functorIsoOfSimplicialHomotopy (functorHomotopyPostcomp H
          (continuousKanReplacementUnit.app X)))
        (continuousKanReplacementUnit.naturality f)
        (continuousKanReplacementUnit.naturality g) := by
  have he := (homotopyIso_precomp L (continuousKanReplacementUnit.app A)).symm
  have hh : ((functorIsoOfSimplicialHomotopy L).precomp
      (continuousKanReplacementUnit.app A)).hom = SSet.Truncated.HomotopyCategory.homMk
        (functorEdgeOfSimplicialHomotopy
          (functorHomotopyPrecomp L (continuousKanReplacementUnit.app A))) := by
    rw [he]
    rfl
  symm
  exact functorIsoOfEq_of_homotopy_h_eq
    (functorHomotopyPostcomp H (continuousKanReplacementUnit.app X))
    (functorHomotopyPrecomp L (continuousKanReplacementUnit.app A)) _ _ rfl hh
    (continuousKanReplacementUnit.naturality f) (continuousKanReplacementUnit.naturality g) hL.symm

/-- 概要：元の単位上の path 類が等しい二つの指定円柱の Kan 延長の同型は等しい。
方針：単位による前合成を忠実性で消去する。
規約：延長は任意、指定類を保持。使われ方：既存の比較候補と底固定模型の照合。 -/
lemma kanHomotopyExtension_iso_eq (H K : SSet.Homotopy f g)
    (L M : SSet.Homotopy (continuousKanReplacement.map f) (continuousKanReplacement.map g))
    (hL : (continuousKanReplacementUnit.app A ▷ (Δ[1] : SSet.{u})) ≫ L.h =
      H.h ≫ continuousKanReplacementUnit.app X)
    (hM : (continuousKanReplacementUnit.app A ▷ (Δ[1] : SSet.{u})) ≫ M.h =
      K.h ≫ continuousKanReplacementUnit.app X)
    (h : SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy
        (functorHomotopyPostcomp H (continuousKanReplacementUnit.app X))) =
      SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy
        (functorHomotopyPostcomp K (continuousKanReplacementUnit.app X)))) :
    functorIsoOfSimplicialHomotopy L = functorIsoOfSimplicialHomotopy M := by
  apply functorIso_precomp_injective_of_weakEquivalence (continuousKanReplacementUnit.app A)
    (continuousKanReplacementUnit_isWeakHomotopyEquivalence A)
  change (functorIsoOfSimplicialHomotopy L).precomp (continuousKanReplacementUnit.app A) =
    (functorIsoOfSimplicialHomotopy M).precomp (continuousKanReplacementUnit.app A)
  rw [kanHomotopyExtension_precomp_iso H L hL, kanHomotopyExtension_precomp_iso K M hM]
  have he : functorIsoOfSimplicialHomotopy (functorHomotopyPostcomp H
      (continuousKanReplacementUnit.app X)) =
      functorIsoOfSimplicialHomotopy (functorHomotopyPostcomp K
        (continuousKanReplacementUnit.app X)) := by
    apply Iso.ext
    exact h
  rw [he]

end SerrePositivity.InfinityCategories.F2
