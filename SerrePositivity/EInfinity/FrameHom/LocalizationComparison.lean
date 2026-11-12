module

public import SerrePositivity.KST.LocalizingInvariants.LocalizationUniqueness
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Roof.PinchedEndpointTransport
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CoherentPinchedTransport

/-!
概要：同じ辺集合の指定された二つの ∞ 局所化の Hom を実比較する。
方針：承認された一般局所化の一意性を読み取り専用で使い、同じ比較射を Hom に適用する。
規約：KST の暫定 import はこの葉に限る。dg 代数の KST モジュールは import しない。
使われ方：一般モデル側の比較を Sp の指定局所化へ移す。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.FrameHom
open CategoryTheory SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial
variable {A Q D : SSet.{u}} [Quasicategory Q] [Quasicategory D]
  (F : A ⟶ Q) (G : A ⟶ D) (W : Set (A _⦋1⦌))
  (hF : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.IsLocalization F W) (hG : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.IsLocalization G W)
  (K : Q ⟶ D) (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (F ≫ K) G)

include F G W hF hG e in
/-- 概要：指定された局所化比較の元の Hom 射は QCat 同値。
方針：同じ比較関手の局所化一意性と全充満忠実性を使う。
規約：比較 K を新しく選ばない。使われ方：実 frame 比較の弱同値性の輸送。 -/
lemma localizationComparison_pinchedHom_isQCatEquivalence (x y : Q _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomMap K x y) := by
  let c := KST.LocalizingInvariants.localizationComparisonEquivalence F G W hF hG K e
  exact (c.isQCatEquivalence.isFullyFaithful x y).isQCatEquivalence

/-- 概要：厳密に可換な局所化比較を元の局所化像の pinched Hom に送る。
方針：同じ K の Hom 射を端点の等式で輸送する。
規約：両方の元の局所化頂点を保持する。使われ方：指定局所化への実比較射。 -/
def localizationPinchedComparison (h : F ≫ K = G) (x y : A _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom (F.app (Opposite.op ⦋0⦌) x) (F.app (Opposite.op ⦋0⦌) y) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom (G.app (Opposite.op ⦋0⦌) x) (G.app (Opposite.op ⦋0⦌) y) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomMap K _ _ ≫ (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Roof.pinchedEndpointIso
    (congrArg (fun t : A ⟶ D => t.app (Opposite.op ⦋0⦌) x) h)
    (congrArg (fun t : A ⟶ D => t.app (Opposite.op ⦋0⦌) y) h)).hom

include W hF hG e in
/-- 概要：元の端点を保持した実局所化 Hom 比較は QCat 同値。
方針：元の Hom 射の充満忠実性と端点輸送の同型性を合成する。
規約：π₀ の比較へ置き換えない。使われ方：元の frame Hom との実合成。 -/
lemma localizationPinchedComparison_isQCatEquivalence
    (h : F ≫ K = G) (x y : A _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (localizationPinchedComparison F G K h x y) := by
  exact (localizationComparison_pinchedHom_isQCatEquivalence F G W hF hG K e _ _).comp
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Roof.pinchedEndpointIso
      (congrArg (fun t : A ⟶ D => t.app (Opposite.op ⦋0⦌) x) h)
      (congrArg (fun t : A ⟶ D => t.app (Opposite.op ⦋0⦌) y) h))).isQCatEquivalence

/-- 概要：指定二胞体を保持した局所化の比較データ。
方針：元の比較関手の同値と同じ三角形を組にする。
規約：三角形を等式へ変更しない。使われ方：Sp における coherent な合成。 -/
structure CoherentLocalizationComparison (F : A ⟶ Q) (G : A ⟶ D) where
  equivalence : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence Q D
  triangle : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (F ≫ equivalence.hom) G

/-- 概要：局所化一意性の同じ K と同じ指定二胞体を公開する。
方針：読み取り専用の一意性定理の元の比較を束ねる。
規約：新しい比較関手や二胞体を選ばない。使われ方：指定局所化への全族輸送。 -/
def localizationComparisonData : CoherentLocalizationComparison F G where
  equivalence := KST.LocalizingInvariants.localizationComparisonEquivalence F G W hF hG K e
  triangle := e

/-- 概要：公開された比較データの三角形は元の指定二胞体そのもの。
方針：束ねの定義を読む。
規約：定義上の等式。使われ方：消費者の二胞体の合成。 -/
lemma localizationComparisonData_triangle :
    (localizationComparisonData F G W hF hG K e).triangle = e := rfl

namespace CoherentLocalizationComparison
variable {F G} (c : CoherentLocalizationComparison F G)

/-- 概要：同じ二胞体の成分に沿った実 pinched Hom の比較同値。
方針：同じ比較関手の Hom 射と可逆な二つの端点成分を合成する。
規約：源には成分の逆、標的には成分自身を使う。
使われ方：実 frame Hom から指定局所化への輸送。 -/
def pinchedEquivalence (x y : A _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom (F.app (Opposite.op ⦋0⦌) x) (F.app (Opposite.op ⦋0⦌) y))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom (G.app (Opposite.op ⦋0⦌) x) (G.app (Opposite.op ⦋0⦌) y)) :=
  ((c.equivalence.isQCatEquivalence.isFullyFaithful _ _).isQCatEquivalence.choose).trans
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.pinchedEndpointEquivalence (c.triangle.toNatIso.app (HomotopyCategory.mk x))
      (c.triangle.toNatIso.app (HomotopyCategory.mk y)))

/-- 概要：実 Hom 比較は同じ K の作用と指定成分の共役。
方針：比較同値の順射を展開する。
規約：元の三角形の両端成分を保持。使われ方：零単体の coherent な照合。 -/
lemma pinchedEquivalence_hom (x y : A _⦋0⦌) :
    (c.pinchedEquivalence x y).hom =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomMap c.equivalence.hom _ _ ≫
        (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.pinchedEndpointEquivalence (c.triangle.toNatIso.app (HomotopyCategory.mk x))
          (c.triangle.toNatIso.app (HomotopyCategory.mk y))).hom := rfl

/-- 概要：指定二胞体の成分は元の全射に自然。
方針：同じ二胞体の自然同型への評価を使う。
規約：hA の任意の射で成立。使われ方：全図式の標的自然性の整合。 -/
lemma triangle_naturality {x y : hoFunctor.obj A} (f : x ⟶ y) :
    (hoFunctor.map (F ≫ c.equivalence.hom)).toFunctor.map f ≫
      (c.triangle.toNatIso.app y).hom =
        (c.triangle.toNatIso.app x).hom ≫ (hoFunctor.map G).toFunctor.map f :=
  c.triangle.toNatIso.hom.naturality f

end CoherentLocalizationComparison

end SerrePositivity.EInfinity.FrameHom
