module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.ResolutionComparisonEquivalence
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.UniverseHomotopy
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.FullyFaithfulEquivalence

/-!
# Dold–Kan coherent nerve と dg nerve の同値

概要：任意の可換環上の dg 圏について、構成済みの比較射は quasicategory の同値である。
方針：標準 Hom の解像の比較のホモトピー逆を移し、充満忠実性と本質的全射性から A3e を使う。
規約：対象の閉零射の通常の圏を DK 豊穣圏の台に用い、比較射は低次の計算と同じもの。
使われ方：HA 1.3.1.13–1.3.1.17、Kerodon 2.5.9（Tag 00SC）、E2b の coherent nerve と dg nerve の接続。

対応節は Kerodon 2.5（Tag 00ND）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
open CategoryTheory DifferentialGraded
variable {R : Type u} [CommRing R] {D : Type v} [DGCategory R D]

/-- 概要：標準座標の実際の pinched 比較射は単体的ホモトピー同値である。
方針：標準 Hom の解像の比較の逆を宇宙の持ち上げで移し、既存の比較の判定を使う。
規約：環と dg 圏以外の前提は追加しない。
使われ方：HA 1.3.1.17 の写像空間の比較。 -/
lemma coherentPinchedStandardComparison_homotopyEquivalence (x y : ClosedCategory R D) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentPinchedStandardComparison (R := R) (D := D) x y) := by
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentPinchedStandardComparison_homotopyEquivalence_iff_resolution x y).mpr
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.ulift_homotopyEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.resolutionComparison_homotopyEquivalence
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardHomSpace (R := R) (D := D) x y))

/-- 概要：元の dg pinched Hom への実際の比較射は単体的ホモトピー同値である。
方針：標準座標の同値性を既存の自然同型に沿って移す。
規約：標準の二つの端点を固定した射そのものに適用する。
使われ方：HA 1.3.1.17 の Core の充満忠実性との接続。 -/
lemma coherentPinchedComparison_homotopyEquivalence (x y : D) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentPinchedComparison (R := R) (D := D) x y) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentPinchedStandardComparison_homotopyEquivalence_iff (R := R) (D := D) x y).mp
    (coherentPinchedStandardComparison_homotopyEquivalence (R := R) (D := D) x y)

/-- 概要：構成済みの coherent nerve から dg nerve への比較射は充満忠実である。
方針：全ての対象間の実際の pinched 比較射のホモトピー同値性を適用する。
規約：判定だけでなく、その右辺を無条件に証明して適用する。
使われ方：HA 1.3.1.17 の A3e への最終の入力。 -/
lemma coherentComparison_fullyFaithful :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentComparison (R := R) (D := D)) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentComparison_fullyFaithful_iff_standard (R := R) (D := D)).mpr
    (fun x y ↦ coherentPinchedStandardComparison_homotopyEquivalence (R := R) (D := D) x y)

/-- 概要：Dold–Kan で豊穣化した dg 圏の coherent nerve と dg nerve の選択した同値。
方針：既存の比較射の充満忠実性と全頂点での本質的全射性を A3e に渡す。
規約：順方向は構成済みの比較射のまま保つ。
使われ方：HA 1.3.1.17、E2b から dg nerve への比較。 -/
def coherentComparisonEquivalence :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.doldKanCoherentNerve (R := R) (D := D)) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R D) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.qCatEquivalenceOfFullyFaithfulEssentiallySurjective (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentComparison (R := R) (D := D))
    coherentComparison_fullyFaithful _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentComparison_essentiallySurjective

/-- 概要：選択した同値の順方向は元の具体的な比較射である。
方針：A3e の選択した逆データの順方向の定義を評価する。
規約：別の射との存在的な同値ではない。
使われ方：HA 1.3.1.17 の低次の計算と選択した同値を接続する。 -/
lemma coherentComparisonEquivalence_hom :
    (coherentComparisonEquivalence (R := R) (D := D)).hom =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentComparison (R := R) (D := D) := rfl

/-- 概要：構成済みの具体的な比較射は quasicategory の同値である。
方針：選択した同値から既存の同値性の命題を取り出す。
規約：環と dg 圏以外の追加条件はない。
使われ方：HA 1.3.1.17 の比較の公開命題。 -/
lemma coherentComparison_isQCatEquivalence :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentComparison (R := R) (D := D)) :=
  (coherentComparisonEquivalence (R := R) (D := D)).isQCatEquivalence

/-- 概要：Kan 複体間で同値な射の厳密な片側の逆は反対側でもホモトピー逆になる。
方針：同値の選択した逆と厳密な片側の逆を可逆二胞体で同定する。
規約：元の片側の逆をそのまま使うホモトピーを得る。
使われ方：Kerodon §4.5.1（Tag 01DQ）、標準 Hom の既存の逆向きの射の確認。 -/
lemma simplicialHomotopy_split_inverse {A B : SSet.{u}} [SSet.KanComplex A] [SSet.KanComplex B]
    (f : A ⟶ B) (g : B ⟶ A) (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence f)
    (hfg : f ≫ g = 𝟙 A) : Nonempty (SSet.Homotopy (g ≫ f) (𝟙 B)) := by
  let e := hf.isQCatEquivalence.choose
  have he : e.hom = f := rfl
  have h : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso e.inv g := by
    simpa only [Category.assoc, he, hfg, Category.comp_id, Category.id_comp] using
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.postcomp e.invHomIso g
  let hi : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (g ≫ f) (𝟙 B) := (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.postcomp h.symm f) ≪≫ e.invHomIso
  exact ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.simplicialHomotopy hi⟩

open SSet.modelCategoryQuillen in
/-- 概要：実際の標準比較射の後に既存の逆構成を取る合成は恒等射とホモトピックである。
方針：全次数の厳密な片側の逆と標準比較射の同値性から、同じ逆射の反対側のホモトピーを得る。
規約：以前に定義した二つの実際の射を使い、新しい逆射に置き換えない。
使われ方：HA 1.3.1.17 の γ1.5d の反対側の合成の完了。 -/
lemma coherentPinchedStandardComparison_oppositeHomotopy (x y : ClosedCategory R D) :
    Nonempty (SSet.Homotopy
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentPinchedStandardComparison (R := R) (D := D) x y ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardHomToCoherentPinched (R := R) (D := D) x y) (𝟙 _)) := by
  have : SSet.KanComplex (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentPinchedHom (R := R) (D := D) x y) :=
    inferInstanceAs (SSet.KanComplex
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentVertex (R := R) (D := D) x) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentVertex (R := R) (D := D) y)))
  have : SSet.KanComplex (SSet.uliftFunctor.{v, u}.obj
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardHomSpace (R := R) (D := D) x y)) := by
    exact HomotopicalAlgebra.isFibrant_of_fibration
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardHomPinchedIso (R := R) (D := D) x y).hom
  apply simplicialHomotopy_split_inverse _ _
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.simplicialHomotopyEquivalence_split_iff _ _
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardHomToCoherentPinched_comp (R := R) (D := D) x y)).mpr
        (coherentPinchedStandardComparison_homotopyEquivalence (R := R) (D := D) x y))
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardHomToCoherentPinched_comp (R := R) (D := D) x y

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
