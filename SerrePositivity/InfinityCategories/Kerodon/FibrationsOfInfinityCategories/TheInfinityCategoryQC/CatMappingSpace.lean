module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CoherentEdgeStructure
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.HomEquivalence
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.HomOrdinary
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.HomEnrichedNaturality

/-!
概要：Cat_∞ の写像空間と関手 ∞ 圏の core の比較同値。
方針：QCat の豊穣 Hom の表示に F1 の coherent Hom 比較を適用する。
規約：core Fun は宇宙 u、Cat_∞ の写像空間は宇宙 u+1 なので ULift して比較する。
使われ方：Cat_∞ の引き戻しの全試験対象に対する写像空間の普遍性。

対応節は Kerodon 5.5（Tag 01YV）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC

/-- 概要：Cat_∞ の二対象間の右写像空間。
方針：既存の CatInfinity の native な右 pinchedHom を用いる。
規約：端点は元の QCat 対象の coherent な頂点。
使われ方：Cat_∞ の極限の写像空間による判定。 -/
def catInfinityMappingSpace (X Y : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.QCat.{u}) : SSet.{u + 1} :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coherentVertex X) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coherentVertex Y)

/-- 概要：Cat_∞ の写像空間は Kan 複体。
方針：CatInfinity の quasicategory 性と右写像空間の既存の Kan 性を使う。
規約：二対象の個別の追加充填仮定はない。
使われ方：写像空間の同値を空間の同値として利用する。 -/
instance catInfinityMappingSpace_kanComplex (X Y : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.QCat.{u}) :
    KanComplex (catInfinityMappingSpace X Y) :=
  inferInstanceAs (KanComplex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex X) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex Y)))

/-- 概要：二つの小さい quasicategory の間の関手 ∞ 圏の core。
方針：全自然変換の関手 ∞ 圏から同値辺の最大 Kan 部分複体を取る。
規約：単体の宇宙は u のままで、通常の関手の同型類による集合ではない。
使われ方：Cat_∞ の豊穣 Hom の具体的な小さい模型。 -/
def catInfinityFunctorCore (X Y : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.QCat.{u}) : SSet.{u} :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore ((ihom X.obj).obj Y.obj)

/-- 概要：関手 ∞ 圏の core は Kan 複体。
方針：関手 ∞ 圏の quasicategory 性と core の Kan 性を使う。
規約：X、Y は QCat の対象であることだけを使う。
使われ方：宇宙を持ち上げた写像空間比較の始域。 -/
instance catInfinityFunctorCore_kanComplex (X Y : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.QCat.{u}) :
    KanComplex (catInfinityFunctorCore X Y) :=
  inferInstanceAs (KanComplex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore ((ihom X.obj).obj Y.obj) : SSet.{u}))

/-- 概要：関手 core から Cat_∞ の写像空間への標準比較射。
方針：QCat の Hom に F1 の全次数で定義された coherent 比較を適用する。
規約：始域の ULift を明示し、標準比較射の向きを保つ。
使われ方：小さい関手空間と Cat_∞ 内の普遍性の橋渡し。 -/
def catInfinityMappingComparison (X Y : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.QCat.{u}) :
    (SSet.uliftFunctor.{u + 1, u}).obj (catInfinityFunctorCore X Y) ⟶
      catInfinityMappingSpace X Y := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentHomComparison X Y

/-- 概要：標準の写像空間比較射は同値。
方針：QCat の全 Hom の Kan 性に coherent Hom 比較定理を適用する。
規約：π₀ だけでなく全単体の写像空間の同値を返す。
使われ方：全試験 ∞ 圏からの写像空間の引き戻し判定。 -/
lemma catInfinityMappingComparison_isQCatEquivalence (X Y : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.QCat.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (catInfinityMappingComparison X Y) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentHomComparison_isQCatEquivalence X Y

/-- 概要：関手 core と Cat_∞ の写像空間の逆射付き同値データ。
方針：F1 の標準比較射の同値データを QCat に適用する。
規約：選択するのは逆射と逆条件であり、順方向の射は標準比較射のまま。
使われ方：Cat_∞ の写像空間の具体的な利用。 -/
def catInfinityMappingEquivalence (X Y : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.QCat.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence ((SSet.uliftFunctor.{u + 1, u}).obj (catInfinityFunctorCore X Y))
      (catInfinityMappingSpace X Y) := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentHomEquivalence X Y

/-- 概要：選択した同値の順方向は元の標準比較射に等しい。
方針：同値データの選択の定義を計算する。
規約：選択された逆射によって順方向を変更しない。
使われ方：比較の自然性を選択済みの同値にも適用する。 -/
lemma catInfinityMappingEquivalence_hom (X Y : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.QCat.{u}) :
    (catInfinityMappingEquivalence X Y).hom = catInfinityMappingComparison X Y := rfl

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
