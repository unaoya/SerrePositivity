module

public import SerrePositivity.InfinityCategories.DoldKanComparison.UniverseHomotopy
public import SerrePositivity.InfinityCategories.Core.FullyFaithfulEquivalence

/-!
# Dold–Kan coherent nerve と dg nerve の同値

概要：任意の可換環上の dg 圏について、構成済みの比較射は quasicategory の同値である。
方針：標準 Hom の解像の比較のホモトピー逆を移し、充満忠実性と本質的全射性から A3e を使う。
規約：対象の閉零射の通常の圏を DK 豊穣圏の台に用い、比較射は低次の計算と同じもの。
使われ方：HA 1.3.1.13–1.3.1.17、Kerodon 2.5.9、E2b の coherent nerve と dg nerve の接続。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.DoldKanComparison
open CategoryTheory DifferentialGraded
variable {R : Type u} [CommRing R] {D : Type v} [DGCategory R D]

/-- 概要：標準座標の実際の pinched 比較射は単体的ホモトピー同値である。
方針：標準 Hom の解像の比較の逆を宇宙の持ち上げで移し、既存の比較の判定を使う。
規約：環と dg 圏以外の前提は追加しない。
使われ方：HA 1.3.1.17 の写像空間の比較。 -/
lemma coherentPinchedStandardComparison_homotopyEquivalence (x y : ClosedCategory R D) :
    IsSimplicialHomotopyEquivalence
      (coherentPinchedStandardComparison (R := R) (D := D) x y) := by
  apply (coherentPinchedStandardComparison_homotopyEquivalence_iff_resolution x y).mpr
  exact ulift_homotopyEquivalence (resolutionComparison_homotopyEquivalence
    (standardHomSpace (R := R) (D := D) x y))

/-- 概要：元の dg pinched Hom への実際の比較射は単体的ホモトピー同値である。
方針：標準座標の同値性を既存の自然同型に沿って移す。
規約：標準の二つの端点を固定した射そのものに適用する。
使われ方：HA 1.3.1.17 の Core の充満忠実性との接続。 -/
lemma coherentPinchedComparison_homotopyEquivalence (x y : D) :
    IsSimplicialHomotopyEquivalence (coherentPinchedComparison (R := R) (D := D) x y) :=
  (coherentPinchedStandardComparison_homotopyEquivalence_iff (R := R) (D := D) x y).mp
    (coherentPinchedStandardComparison_homotopyEquivalence (R := R) (D := D) x y)

/-- 概要：構成済みの coherent nerve から dg nerve への比較射は充満忠実である。
方針：全ての対象間の実際の pinched 比較射のホモトピー同値性を適用する。
規約：判定だけでなく、その右辺を無条件に証明して適用する。
使われ方：HA 1.3.1.17 の A3e への最終の入力。 -/
lemma coherentComparison_fullyFaithful :
    IsFullyFaithful (coherentComparison (R := R) (D := D)) :=
  (coherentComparison_fullyFaithful_iff_standard (R := R) (D := D)).mpr
    (fun x y ↦ coherentPinchedStandardComparison_homotopyEquivalence (R := R) (D := D) x y)

/-- 概要：Dold–Kan で豊穣化した dg 圏の coherent nerve と dg nerve の選択した同値。
方針：既存の比較射の充満忠実性と全頂点での本質的全射性を A3e に渡す。
規約：順方向は構成済みの比較射のまま保つ。
使われ方：HA 1.3.1.17、E2b から dg nerve への比較。 -/
def coherentComparisonEquivalence :
    QCatEquivalence (doldKanCoherentNerve (R := R) (D := D)) (dgNerve R D) :=
  qCatEquivalenceOfFullyFaithfulEssentiallySurjective (coherentComparison (R := R) (D := D))
    coherentComparison_fullyFaithful coherentComparison_essentiallySurjective

/-- 概要：選択した同値の順方向は元の具体的な比較射である。
方針：A3e の選択した逆データの順方向の定義を評価する。
規約：別の射との存在的な同値ではない。
使われ方：HA 1.3.1.17 の低次の計算と選択した同値を接続する。 -/
lemma coherentComparisonEquivalence_hom :
    (coherentComparisonEquivalence (R := R) (D := D)).hom =
      coherentComparison (R := R) (D := D) := rfl

/-- 概要：構成済みの具体的な比較射は quasicategory の同値である。
方針：選択した同値から既存の同値性の命題を取り出す。
規約：環と dg 圏以外の追加条件はない。
使われ方：HA 1.3.1.17 の比較の公開命題。 -/
lemma coherentComparison_isQCatEquivalence :
    IsQCatEquivalence (coherentComparison (R := R) (D := D)) :=
  (coherentComparisonEquivalence (R := R) (D := D)).isQCatEquivalence

/-- 概要：Kan 複体間で同値な射の厳密な片側の逆は反対側でもホモトピー逆になる。
方針：同値の選択した逆と厳密な片側の逆を可逆二胞体で同定する。
規約：元の片側の逆をそのまま使うホモトピーを得る。
使われ方：Kerodon §4.5.1、標準 Hom の既存の逆向きの射の確認。 -/
lemma simplicialHomotopy_split_inverse {A B : SSet.{u}} [SSet.KanComplex A] [SSet.KanComplex B]
    (f : A ⟶ B) (g : B ⟶ A) (hf : IsSimplicialHomotopyEquivalence f)
    (hfg : f ≫ g = 𝟙 A) : Nonempty (SSet.Homotopy (g ≫ f) (𝟙 B)) := by
  let e := hf.isQCatEquivalence.choose
  have he : e.hom = f := rfl
  have h : FunctorIso e.inv g := by
    simpa only [Category.assoc, he, hfg, Category.comp_id, Category.id_comp] using
      FunctorIso.postcomp e.invHomIso g
  let hi : FunctorIso (g ≫ f) (𝟙 B) := (FunctorIso.postcomp h.symm f) ≪≫ e.invHomIso
  exact ⟨FunctorIso.simplicialHomotopy hi⟩

open SSet.modelCategoryQuillen in
/-- 概要：実際の標準比較射の後に既存の逆構成を取る合成は恒等射とホモトピックである。
方針：全次数の厳密な片側の逆と標準比較射の同値性から、同じ逆射の反対側のホモトピーを得る。
規約：以前に定義した二つの実際の射を使い、新しい逆射に置き換えない。
使われ方：HA 1.3.1.17 の γ1.5d の反対側の合成の完了。 -/
lemma coherentPinchedStandardComparison_oppositeHomotopy (x y : ClosedCategory R D) :
    Nonempty (SSet.Homotopy
      (coherentPinchedStandardComparison (R := R) (D := D) x y ≫
        standardHomToCoherentPinched (R := R) (D := D) x y) (𝟙 _)) := by
  have : SSet.KanComplex (coherentPinchedHom (R := R) (D := D) x y) :=
    inferInstanceAs (SSet.KanComplex
      (pinchedHom (coherentVertex (R := R) (D := D) x) (coherentVertex (R := R) (D := D) y)))
  have : SSet.KanComplex (SSet.uliftFunctor.{v, u}.obj
      (standardHomSpace (R := R) (D := D) x y)) := by
    exact HomotopicalAlgebra.isFibrant_of_fibration
      (standardHomPinchedIso (R := R) (D := D) x y).hom
  apply simplicialHomotopy_split_inverse _ _
    ((simplicialHomotopyEquivalence_split_iff _ _
      (standardHomToCoherentPinched_comp (R := R) (D := D) x y)).mpr
        (coherentPinchedStandardComparison_homotopyEquivalence (R := R) (D := D) x y))
  exact standardHomToCoherentPinched_comp (R := R) (D := D) x y

end SerrePositivity.InfinityCategories.DoldKanComparison
