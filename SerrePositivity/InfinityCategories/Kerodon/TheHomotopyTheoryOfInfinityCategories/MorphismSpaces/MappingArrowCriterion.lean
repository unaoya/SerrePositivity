module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.MappingArrowOfUnit

/-!
概要：coherent な矢印比較による随伴の存在判定。
方針：単位候補から全矢印の比較を構成し、逆向きには各点の条件から単位を抽出する。
規約：この具体的な比較模型を使い、任意の点ごとの同値の族へ弱めない。
使われ方：B1 の自然な写像空間の特徴づけを pinched 模型へ接続する。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
namespace MappingArrowComparison
variable {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
variable {F : X ⟶ Y} {G : Y ⟶ X}

/-- 概要：指定単位の各点の同値性は構成した coherent 比較へ移る。
方針：構成した比較からの単位の回収と標準比較との照合を使う。
規約：同値条件は各点だけ。使われ方：随伴から比較への順方向。 -/
lemma ofUnitHom_isPointwiseEquivalence (η : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (𝟙 X) (F ≫ G))
    (hη : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.UnitMappingSpaceCondition η) : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.MappingArrowComparison.ofUnitHom η).IsPointwiseEquivalence := by
  apply ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.MappingArrowComparison.ofUnitHom η).isPointwiseEquivalence_iff_unitMappingSpaceCondition).mpr
  rwa [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.MappingArrowComparison.ofUnitHom_unitHom]

/-- 概要：coherent な矢印比較の各点の射を右 pinched 模型へ移す。
方針：区間模型との同値で順写像を移す。
規約：端点は x,y、全体の coherence は元の比較が保持する。
使われ方：当初の写像空間による随伴の特徴づけの型。 -/
def pinchedMap (q : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.MappingArrowComparison F G) (x : X _⦋0⦌) (y : Y _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom (F.app (Opposite.op ⦋0⦌) x) y ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom x (G.app (Opposite.op ⦋0⦌) y) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.liftMap (q.intervalMap x y)

/-- 概要：coherent な比較の各点の条件は右 pinched 模型でも同じ。
方針：模型比較の同値性を両端で相殺する。
規約：ホモトピー逆の存在を使う。使われ方：pinched 型での存在判定。 -/
lemma isPointwiseEquivalence_iff_pinched (q : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.MappingArrowComparison F G) :
    q.IsPointwiseEquivalence ↔
      ∀ (x : X _⦋0⦌) (y : Y _⦋0⦌), _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (q.pinchedMap x y) := by
  constructor
  · intro h x y
    exact ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.PinchedInterval.liftMap_isQCatEquivalence_iff (q.intervalMap x y)).mpr
      (h x y).isQCatEquivalence).isSimplicialHomotopyEquivalence
  · intro h x y
    exact ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.PinchedInterval.liftMap_isQCatEquivalence_iff (q.intervalMap x y)).mp
      (h x y).isQCatEquivalence).isSimplicialHomotopyEquivalence

/-- 概要：pinched 比較は抽出単位の標準 pinched 比較と同型。
方針：区間比較と標準単位比較のホモトピーを模型比較で移す。
規約：h Fun の同型で述べる。使われ方：元の自然な比較と構成した随伴の照合。 -/
def pinchedMap_unitIso (q : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.MappingArrowComparison F G) (x : X _⦋0⦌) (y : Y _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (q.pinchedMap x y) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitPinchedMap q.unitHom x y) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.liftMapIso
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorIsoOfSimplicialHomotopy (q.intervalMap_unitIntervalMap_homotopy x y).some)

end MappingArrowComparison

/-- 概要：随伴が存在することと、各点で同値な coherent 矢印比較が存在することは同値。
方針：随伴の単位からの比較と、比較から抽出した単位の局所判定を双方向に適用する。
規約：単位を事前に入力せず、全パラメータの全単射も仮定しない。
使われ方：B1 の具体的な coherent 比較模型での存在判定。 -/
lemma qcat_nonempty_adjunction_iff_exists_mappingArrowComparison
    {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y] (F : X ⟶ Y) (G : Y ⟶ X) :
    Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction F G) ↔
      ∃ q : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.MappingArrowComparison F G, q.IsPointwiseEquivalence := by
  constructor
  · rintro ⟨a⟩
    exact ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.MappingArrowComparison.ofUnitHom a.unitHom,
      MappingArrowComparison.ofUnitHom_isPointwiseEquivalence a.unitHom a.unitMappingSpaceCondition⟩
  · rintro ⟨q, hq⟩
    exact ⟨q.adjunctionOfPointwiseEquivalence hq⟩

/-- 概要：右 pinched 写像空間の同値を持つ coherent 比較による随伴の存在判定。
方針：区間模型での存在判定を pinched 模型へ移す。
規約：coherence は両端を保つ一つの矢印空間の射で指定する。
使われ方：単位を先に指定しない写像空間の特徴づけの具体形。 -/
lemma qcat_nonempty_adjunction_iff_exists_pinchedMappingArrowComparison
    {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y] (F : X ⟶ Y) (G : Y ⟶ X) :
    Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction F G) ↔
      ∃ q : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.MappingArrowComparison F G,
        ∀ (x : X _⦋0⦌) (y : Y _⦋0⦌), _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (q.pinchedMap x y) := by
  rw [qcat_nonempty_adjunction_iff_exists_mappingArrowComparison]
  exact exists_congr (fun q => q.isPointwiseEquivalence_iff_pinched)

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
