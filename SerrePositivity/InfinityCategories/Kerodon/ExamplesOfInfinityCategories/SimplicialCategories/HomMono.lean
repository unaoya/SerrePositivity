module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.MaximumFlag

/-!
概要：coherent nerve の Hom 比較射の単射性。
方針：最初と最後の頂点の間の Hom を旗で評価して元の単体を回収する。
規約：局所 Kan 性を仮定しない。同値性には別に高次の相対拡張を要する。
使われ方：Kerodon Construction 4.6.7.3（Tag 01LD）、Theorem 4.6.7.5（Tag 01LE）、比較の相対的な同値性の証明。

対応節は Kerodon 2.4（Tag 00JN）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u v w
open CategoryTheory SimplicialThickening SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories

/-- 概要：等しい豊穣関手の Hom の作用は依存した型を含めて等しい。
方針：豊穣関手の等号を消去する。
規約：対象の像が変わるので異種等号で述べる。
使われ方：Kerodon §2.4.3（Tag 00KM）、比較した coherent 単体から Hom の作用を取り出す。 -/
lemma enrichedFunctor_map_heq {A : Type w} {C : Type v}
    [EnrichedCategory SSet.{u} A] [EnrichedCategory SSet.{u} C]
    {F G : EnrichedFunctor SSet.{u} A C} (h : F = G) (i j : A) :
    HEq (F.map i j) (G.map i j) := by
  subst G
  rfl

/-- 概要：豊穣 Hom の単体から coherent な単体を作る比較は単射。
方針：端点間の Hom の作用を比較し、最大元座標の旗の切断で元の Yoneda 射を回収する。
規約：全ての次数 n で成り立つ。
使われ方：Kerodon Theorem 4.6.7.5（Tag 01LE）、比較射を包含として扱う準備。 -/
lemma coherentHomComparisonSimplex_injective {C : Type v} [Category.{u} C]
    [SimplicialCategory C] {X Y : C} (n : ℕ) :
    Function.Injective (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomComparisonSimplex (X := X) (Y := Y) (n := n)) := by
  intro σ τ h
  have hm : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomComparisonHom σ (0 : Fin (n + 1)).castSucc
      (Fin.last (n + 1)) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomComparisonHom τ (0 : Fin (n + 1)).castSucc (Fin.last (n + 1)) :=
    eq_of_heq (enrichedFunctor_map_heq h
      (⟨ULift.up (0 : Fin (n + 1)).castSucc⟩ :
        SimplicialThickening (ULift.{u} (Fin (n + 2))))
      ⟨ULift.up (Fin.last (n + 1))⟩)
  have hnorm := congrArg (fun f ↦ f ≫ eqToHom
    (congrArg₂ SimplicialCategory.sHom (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomComparisonObj_cast X Y 0)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomComparisonObj_last X Y n))) hm
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentHomComparisonHom_cast_last, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentHomComparisonHom_cast_last] at hnorm
  apply (SSet.yonedaEquiv (X := SimplicialCategory.sHom X Y) (n := ⦋n⦌)).symm.injective
  have hf := congrArg (fun f ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.maximumFlagMap.{u} n ≫ f) hnorm
  simpa only [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.maximumFlagMap_comp_pathLastMaximumMap,
    Category.id_comp] using hf

/-- 概要：豊穣 Hom から右 pinched 写像空間への比較射は単射。
方針：各次数で ULift を戻し、元の coherent 単体の比較の単射性を使う。
規約：単体的圏の局所 Kan 性を仮定しない。
使われ方：Kerodon Theorem 4.6.7.5（Tag 01LE）、比較の相対拡張の始域の包含。 -/
instance coherentHomComparison_mono {C : Type v} [Category.{u} C] [SimplicialCategory C]
    (X Y : C) : Mono (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentHomComparison X Y) := by
  rw [NatTrans.mono_iff_mono_app]
  rintro ⟨⟨n⟩⟩
  rw [mono_iff_injective]
  intro σ τ h
  apply ULift.ext
  apply coherentHomComparisonSimplex_injective n
  exact congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.Simplex.val h

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories
