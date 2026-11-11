module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.ResolutionHomIso

/-!
# 解像の標準比較射による充満忠実性の判定

概要：実際の dg 比較の写像空間の同値性は、標準 Hom に対する解像の比較射の同値性に等しい。
方針：厳密な片側の逆と Kan 複体の二つから三つ目を得る性質を、解像の同型と合成する。
規約：判定の右辺の位相的な主張を証明するまでは充満忠実性を主張しない。
使われ方：HA 1.3.1.17、Kerodon Theorem 4.6.7.5（Tag 01LE） の解像の同値性との接続。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
open CategoryTheory DifferentialGraded
variable {R : Type u} [CommRing R] {D : Type v} [DGCategory R D]

/-- 概要：Kan 複体間で厳密な片側の逆を持つ二射は同じホモトピー同値性を持つ。
方針：恒等合成の同値性と quasicategory の二つから三つ目を得る性質を使う。
規約：両側の主張とも実際の単体的ホモトピー逆の存在である。
使われ方：Kerodon §4.5.1（Tag 01DQ） の同値の計算を標準 Hom の比較に適用する。 -/
lemma simplicialHomotopyEquivalence_split_iff {A B : SSet.{u}}
    [SSet.KanComplex A] [SSet.KanComplex B] (f : A ⟶ B) (g : B ⟶ A)
    (hfg : f ≫ g = 𝟙 A) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence f ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence g := by
  have hi : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (f ≫ g) := by
    rw [hfg]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.simplicialHomotopyEquivalence_iso_hom (Iso.refl A)
  constructor
  · intro hf
    exact (hf.isQCatEquivalence.cancel_left hi.isQCatEquivalence).isSimplicialHomotopyEquivalence
  · intro hg
    exact (hg.isQCatEquivalence.cancel_right hi.isQCatEquivalence).isSimplicialHomotopyEquivalence

open SSet.modelCategoryQuillen in
/-- 概要：標準座標の dg 比較射の同値性は解像の標準比較射の同値性と同じである。
方針：片側の逆で逆向きの射へ移し、解像の同型との可換式を使う。
規約：右随伴の Kan 性は実際の coherent pinched Hom との同型から導く。
使われ方：HA 1.3.1.17 の充満忠実性を解像の位相的な比較へ帰着する。 -/
lemma coherentPinchedStandardComparison_homotopyEquivalence_iff_resolution
    (x y : ClosedCategory R D) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentPinchedStandardComparison (R := R) (D := D) x y) ↔
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (SSet.uliftFunctor.{v, u}.map
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionComparison (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardHomSpace (R := R) (D := D) x y))) := by
  have : SSet.KanComplex (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentPinchedHom (R := R) (D := D) x y) :=
    inferInstanceAs (SSet.KanComplex
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentVertex (R := R) (D := D) x) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentVertex (R := R) (D := D) y)))
  have : SSet.KanComplex (SSet.uliftFunctor.{v, u}.obj
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardHomSpace (R := R) (D := D) x y)) := by
    exact HomotopicalAlgebra.isFibrant_of_fibration
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardHomPinchedIso (R := R) (D := D) x y).hom
  have : SSet.KanComplex (SSet.uliftFunctor.{v, u}.obj
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionRightAdjoint.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardHomSpace (R := R) (D := D) x y))) := by
    exact HomotopicalAlgebra.isFibrant_of_fibration (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.resolutionHomIso x y).inv
  calc
    _ ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardHomToCoherentPinched (R := R) (D := D) x y) :=
      (simplicialHomotopyEquivalence_split_iff _ _ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardHomToCoherentPinched_comp x y)).symm
    _ ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardHomToCoherentPinched (R := R) (D := D) x y ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.resolutionHomIso x y).hom) :=
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.simplicialHomotopyEquivalence_postcomp_iso_iff _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.resolutionHomIso x y)).symm
    _ ↔ _ := by rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.standardHomToCoherentPinched_resolutionHomIso]

/-- 概要：dg 比較写像の充満忠実性は全 Hom の解像の標準比較射の同値性と同値である。
方針：標準 Hom での既存の判定へ解像の判定を各対象の組で適用する。
規約：対象の組全てで実際の単体的ホモトピー逆が必要。
使われ方：HA 1.3.1.17 の A3e への接続の残る位相的な証明条件。 -/
lemma coherentComparison_fullyFaithful_iff_resolution :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentComparison (R := R) (D := D)) ↔
      ∀ x y : D, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (SSet.uliftFunctor.{v, u}.map
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionComparison (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardHomSpace (R := R) (D := D) x y))) := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentComparison_fullyFaithful_iff_standard]
  exact forall_congr' (fun x ↦ forall_congr' (fun y ↦
    coherentPinchedStandardComparison_homotopyEquivalence_iff_resolution x y))

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
