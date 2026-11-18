module

public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftStraighteningRepresentationBaseChangeLaw
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftPullbackLimitTransport
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.FunctorIsoWhiskerExchange

/-!
概要：元の引き戻し分類同型を、同じ指定表現上の底写像の同型へ照合する。
方針：指定βの表現比較との両立と、同じ全関手同型の前後合成の交換則を使う。
規約：HTT §3.3.2・Kerodon Tag 028Tの既存構成の特殊な法則。
使われ方：R04で元の分類同型の極限頂点の射を計算する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory Limits SSet
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence
open SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries
open SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- 同じ両端の指定比較を通す共役は、同じ交換四角形に沿って正規化される。 -/
private lemma iso_conjugation_square {𝒞 : Type u} [Category.{v} 𝒞]
    {a b c d r s : 𝒞} (bf : a ≅ b) (bg : c ≅ d) (z : a ≅ c)
    (ef : b ≅ r) (eg : d ≅ s) (f : a ≅ r) (g : c ≅ s) (k : r ≅ s)
    (hf : bf ≪≫ ef = f) (hg : bg ≪≫ eg = g) (hn : z ≪≫ g = f ≪≫ k) :
    (bf.symm ≪≫ z ≪≫ bg) ≪≫ eg = ef ≪≫ k := by
  calc
    _ = bf.symm ≪≫ z ≪≫ g := by
      simp only [Iso.trans_assoc]
      rw [hg]
    _ = bf.symm ≪≫ f ≪≫ k := by rw [hn]
    _ = _ := by
      rw [← hf]
      simp only [← Iso.trans_assoc, Iso.symm_self_id, Iso.refl_trans]

/-- 元の引き戻し分類同型は、同じ表現と元の底写像の同型の作用で計算できる。
HTT §3.3.2・Kerodon Tag 028Tの構成の、この指定表現での合成・移送の法則。 -/
@[cite HTT "3.3.2" (partial := special) "引き戻しの指定分類同型と元の表現比較の交換四角形。"]
lemma leftPullbackClassificationIso_representation_naturality
    {E B K : SSet.{u}} [Quasicategory B] [Quasicategory K]
    (p : E ⟶ B) [LeftFibration p] {f g : K ⟶ B} (e : FunctorIso f g)
    (R : LeftTransportRepresentation ((SSet.uliftFunctor.{u+1,u}).map p)) :
    leftPullbackClassificationIso p e ≪≫
      leftStraighteningInfinityDiagram_representationIso (pullback.snd p g) (R.nativeRestrict g) =
    leftStraighteningInfinityDiagram_representationIso (pullback.snd p f) (R.nativeRestrict f) ≪≫
      (functorIso_ulift.{u,u+1} e).postcomp R.diagram := by
  let U := SSet.uliftFunctor.{u+1,u}
  let bf := leftStraighteningInfinityDiagram_baseChangeIso p f
  let bg := leftStraighteningInfinityDiagram_baseChangeIso p g
  let η := leftStraighteningInfinityDiagram_representationIso p R
  let ef := leftStraighteningInfinityDiagram_representationIso (pullback.snd p f) (R.nativeRestrict f)
  let eg := leftStraighteningInfinityDiagram_representationIso (pullback.snd p g) (R.nativeRestrict g)
  let z := (functorIso_ulift.{u,u+1} e).postcomp (leftStraighteningInfinityDiagram p)
  change (bf.symm ≪≫ z ≪≫ bg) ≪≫ eg = ef ≪≫ (functorIso_ulift.{u,u+1} e).postcomp R.diagram
  exact iso_conjugation_square bf bg z ef eg (η.precomp (U.map f)) (η.precomp (U.map g))
    ((functorIso_ulift.{u,u+1} e).postcomp R.diagram)
    (leftStraighteningInfinityDiagram_representationIso_baseChange p f R)
    (leftStraighteningInfinityDiagram_representationIso_baseChange p g R)
    (functorIso_whisker_exchange (functorIso_ulift.{u,u+1} e) η)

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
