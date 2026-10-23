module

public import SerrePositivity.InfinityCategories.F1.Yoneda.PresheafDensity.Support.ContinuousKanWeakEquivalence
public import SerrePositivity.InfinityCategories.F1B.KanHomotopyClasses
public import SerrePositivity.InfinityCategories.F1B.HomotopyWhiskering

/-!
概要：具体的な連続 Kan 置換は射のホモトピー関係を保つ。
方針：単位による自然性と前合成の単射性で、元のホモトピーを反映する。
規約：Kan 置換を単体的豊穣関手として仮定しない。
使われ方：全空間の有限図式を fiber へ移すホモトピーの Kan 置換後の比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.F2

/-- 概要：連続 Kan 置換は任意の二射のホモトピー関係を保つ。
方針：始域の単位の弱同値で写像空間の連結成分の等式を反映する。
規約：元の始域・終域に充填性を要求しない。使われ方：有限 fiber 検出の移送。 -/
lemma continuousKanReplacement_map_homotopy {A X : SSet.{u}} {f g : A ⟶ X}
    (H : SSet.Homotopy f g) :
    Nonempty (SSet.Homotopy (continuousKanReplacement.map f)
      (continuousKanReplacement.map g)) := by
  apply (functorVertex_piZero_eq_iff_homotopy _ _).1
  apply (continuousKanReplacementUnit_isWeakHomotopyEquivalence A
    (continuousKanReplacement.obj X)).injective
  change SSet.π₀.mk (functorVertex
      (continuousKanReplacementUnit.app A ≫ continuousKanReplacement.map f)) =
    SSet.π₀.mk (functorVertex
      (continuousKanReplacementUnit.app A ≫ continuousKanReplacement.map g))
  rw [← continuousKanReplacementUnit.naturality f,
    ← continuousKanReplacementUnit.naturality g]
  exact (functorVertex_piZero_eq_iff_homotopy _ _).2
    ⟨functorHomotopyPostcomp H (continuousKanReplacementUnit.app X)⟩

end SerrePositivity.InfinityCategories.F2
