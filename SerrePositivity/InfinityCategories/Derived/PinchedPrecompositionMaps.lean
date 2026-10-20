module
public import SerrePositivity.InfinityCategories.Derived.DGClosedPrecompositionNaturality
public import SerrePositivity.InfinityCategories.Derived.PinchedChainMapComposition

/-! # 閉前合成の全単体写像の自然性

概要：閉分母の前合成と商の比較が、各単体だけでなく全単体写像として可換である。
方針：Hom 鎖写像の等式に、実 pinched 写像の合成則を適用する。
規約：前合成は全ての面・退化を一括で保つ。使われ方：相対骨格の下次数の更新。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
variable (A : Type u) [CommRing A] (D E : Type v) [DGCategory A D] [DGCategory A E]
variable [Small.{u} D] [Small.{u} E]

/-- 閉前合成と dg 関手の比較は全単体写像として厳密に可換。 -/
lemma pinchedClosedPrecomposition_map_naturality (F : DGFunctor A D E) {q x y : D}
    (r : ForgetEnrichment.of (Complex A) q ⟶ ForgetEnrichment.of (Complex A) x) :
    pinchedClosedPrecomposition A D (y := y) r ≫ pinchedHomChainMap (F.map q y) =
      pinchedHomChainMap (F.map x y) ≫ pinchedClosedPrecomposition A E
        (y := F.obj y) (F.onClosed.map r) := by
  change pinchedHomChainMap (dgClosedPrecomposition A D (y := y) r) ≫ _ =
    _ ≫ pinchedHomChainMap (dgClosedPrecomposition A E (y := F.obj y) (F.onClosed.map r))
  rw [← pinchedHomChainMap_comp, ← pinchedHomChainMap_comp,
    dgClosedPrecomposition_naturality]

/-- 二本の閉分母の前合成は、合成分母の全単体前合成と一致する。 -/
lemma pinchedClosedPrecomposition_map_comp {p q x y : D}
    (r : ForgetEnrichment.of (Complex A) p ⟶ ForgetEnrichment.of (Complex A) q)
    (s : ForgetEnrichment.of (Complex A) q ⟶ ForgetEnrichment.of (Complex A) x) :
    pinchedClosedPrecomposition A D (y := y) s ≫ pinchedClosedPrecomposition A D r =
      pinchedClosedPrecomposition A D (y := y) (r ≫ s) := by
  change pinchedHomChainMap (dgClosedPrecomposition A D s) ≫
    pinchedHomChainMap (dgClosedPrecomposition A D r) = _
  rw [← pinchedHomChainMap_comp, dgClosedPrecomposition_comp]
  rfl

end SerrePositivity.InfinityCategories
