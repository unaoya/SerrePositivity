module

public import SerrePositivity.InfinityCategories.F1.Yoneda.PresheafDensity.Support.ContinuousKanWeakEquivalence
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.FilteredNullHomotopy
public import SerrePositivity.InfinityCategories.F1B.KanComplex.HomotopyClasses
public import SerrePositivity.InfinityCategories.F1B.Homotopy.HomotopyWhiskering

/-!
概要：余錐を持つ射を連続 Kan 置換で送ると定値射と同じホモトピー類になる。
方針：元の余錐の収縮を単位で送り、始域の単位の弱同値性で反映する。
規約：余錐の頂点の単位による像を定値射の値とする。
使われ方：有限部分複体の包含の収縮から置換後の境界の充填を得る。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 概要：余錐を持つ射の Kan 置換後の像は定値射と同じ写像空間の成分に属する。
方針：元の余錐の収縮と単位の自然性を、始域の弱同値による単射性で持ち上げる。
規約：A 自体の Kan 性や有限性は仮定しない。
使われ方：一般の filtered ∞ 圏の弱可縮性の有限部分の収縮。 -/
lemma continuousKanReplacement_map_null_of_cocone {A C : SSet.{u}}
    (f : A ⟶ C) (c : JoinCocone f) :
    ∃ x : (continuousKanReplacement.obj C) _⦋0⦌,
      SSet.π₀.mk (functorVertex (continuousKanReplacement.map f)) =
        SSet.π₀.mk (functorVertex (SSet.const x)) := by
  let x := (continuousKanReplacementUnit.app C).app (Opposite.op ⦋0⦌) c.vertex
  refine ⟨x, ?_⟩
  apply (continuousKanReplacementUnit_isWeakHomotopyEquivalence A
    (continuousKanReplacement.obj C)).injective
  change SSet.π₀.mk (functorVertex
      (continuousKanReplacementUnit.app A ≫ continuousKanReplacement.map f)) =
    SSet.π₀.mk (functorVertex (continuousKanReplacementUnit.app A ≫ SSet.const x))
  have hn : f ≫ continuousKanReplacementUnit.app C =
      continuousKanReplacementUnit.app A ≫ continuousKanReplacement.map f :=
    continuousKanReplacementUnit.naturality f
  rw [← hn, SSet.comp_const]
  change SSet.π₀.mk (functorVertex (f ≫ continuousKanReplacementUnit.app C)) =
    SSet.π₀.mk (functorVertex (SSet.const x))
  let H := functorHomotopyPostcomp (coconeNullHomotopy c) (continuousKanReplacementUnit.app C)
  have hh := (functorVertex_piZero_eq_iff_homotopy _ _).2 ⟨H⟩
  simpa only [SSet.const_comp] using! hh

end SerrePositivity.InfinityCategories.F2
