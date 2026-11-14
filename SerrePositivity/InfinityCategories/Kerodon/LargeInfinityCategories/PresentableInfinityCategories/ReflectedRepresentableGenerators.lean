module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PresentablePresheafReflection
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.PinchedObjectNaturality
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.YonedaPresheafEvaluation

/-!
概要：前層反映の表現可能対象を移した、小さい生成族の候補と写像空間の比較。
方針：同じ左随伴の対象写像と指定された adjunct 比較を使う。
規約：添字は元の小さい底の頂点で、対象ごとに反映表示を選び直さない。
使われ方：G14 の検出族を Yoneda 評価へ接続する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

variable {A : SSet.{u}} [Quasicategory A] {E : SSet.{u + 1}} [Quasicategory E]
  {L : PresheafInfinity A ⟶ E} {R : E ⟶ PresheafInfinity A}

/-- 表現可能前層を同じ左随伴で移した、元の小さい頂点型を添字とする族。 -/
def reflectedRepresentable (L : PresheafInfinity A ⟶ E) (y : A _⦋0⦌) : E _⦋0⦌ :=
  L.app (Opposite.op ⦋0⦌) (functorVertex (representablePresheafInfinity y))

/-- 反映した表現可能対象からの写像空間を、同じ右随伴の像への写像空間に送る。 -/
def reflectedRepresentableMapping (a : QCatAdjunction L R) (y : A _⦋0⦌) (x : E _⦋0⦌) :
    Basic.pinchedHom (reflectedRepresentable L y) x ⟶
      Basic.pinchedHom (functorVertex (representablePresheafInfinity y))
        (R.app (Opposite.op ⦋0⦌) x) :=
  a.pinchedMap (functorVertex (representablePresheafInfinity y)) x

/-- 指定された adjunct 比較は、全写像空間の同値である。 -/
lemma reflectedRepresentableMapping_isQCatEquivalence (a : QCatAdjunction L R)
    (y : A _⦋0⦌) (x : E _⦋0⦌) :
    IsQCatEquivalence (reflectedRepresentableMapping a y x) :=
  (a.pinchedMap_isSimplicialHomotopyEquivalence
    (functorVertex (representablePresheafInfinity y)) x).isQCatEquivalence

/-- 生成族の adjunct 比較は、元の標的の任意の射の後合成に全族で自然。 -/
def reflectedRepresentableMapping_naturality (a : QCatAdjunction L R)
    (y : A _⦋0⦌) {x x' : E _⦋0⦌}
    (f : (HomotopyCategory.mk x : hoFunctor.obj E) ⟶ HomotopyCategory.mk x') :
    FunctorIso
      (postcompose (reflectedRepresentable L y) f ≫ reflectedRepresentableMapping a y x')
      (reflectedRepresentableMapping a y x ≫
        postcompose (functorVertex (representablePresheafInfinity y))
          ((hoFunctor.map R).toFunctor.map f)) :=
  a.pinchedMapNaturalityRightIso (functorVertex (representablePresheafInfinity y)) f

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
