module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.VertexFiberSquareComparison
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.ComparisonFiberSource

/-!
概要：比較射の標的への後合成が導来 fiber に誘導する実際の射と同値性。
方針：可逆 path を後合成し、path 置換の全空間と底の正方形から fiber の射を作る。
規約：標的の比較が同値なら fiber の比較も同値。元の比較射の fibration 性は不要。
使われ方：HTT 4.2.4.1、Kerodon 7.4.1.6（Tag 05QS）・7.5.4.6（Tag 03BB）、錐の切断模型の標的の変更。

対応節は Kerodon 7.4（Tag 02SX）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces
noncomputable section

/-- 概要：標的への後合成が path 置換の全空間に誘導する射。
方針：path の後合成と元の源成分を引き戻しへ持ち上げる。
規約：元の源の点は変更しない。
使われ方：導来 fiber の標的を変更する比較の全空間の射。 -/
def comparisonPathReplacementPost {E B D : SSet.{u}} (p : E ⟶ B) (g : B ⟶ D) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacement p ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacement (p ≫ g) :=
  pullback.lift
    (pullback.fst (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint B 0) p ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathMap g)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementProjection p) (by
      rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathMap_endpoint, ← Category.assoc,
        pullback.condition, Category.assoc]
      rfl)

/-- 概要：path 置換の後合成の比較は path の後合成と可換。
方針：引き戻しへの持ち上げの第一成分を計算する。
規約：可逆 path の既存の後合成を使う。
使われ方：導来 fiber の比較の path 成分。 -/
lemma comparisonPathReplacementPost_path {E B D : SSet.{u}} (p : E ⟶ B) (g : B ⟶ D) :
    comparisonPathReplacementPost p g ≫ pullback.fst (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint D 0) (p ≫ g) =
      pullback.fst (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint B 0) p ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathMap g := pullback.lift_fst ..

/-- 概要：path 置換の後合成の比較は元の源成分を保つ。
方針：引き戻しへの持ち上げの第二成分を計算する。
規約：元の源 E への厳密な等式。
使われ方：全空間の比較の同値性の検証。 -/
lemma comparisonPathReplacementPost_source {E B D : SSet.{u}} (p : E ⟶ B) (g : B ⟶ D) :
    comparisonPathReplacementPost p g ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementProjection (p ≫ g) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementProjection p := pullback.lift_snd ..

/-- 概要：path 置換の後合成の比較は終点の g による像と可換。
方針：path 成分と可逆 path の端点評価の自然性を使う。
規約：底の射は g そのもの。
使われ方：底の頂点を g の像へ移す導来 fiber の射。 -/
lemma comparisonPathReplacementPost_target {E B D : SSet.{u}} (p : E ⟶ B) (g : B ⟶ D) :
    comparisonPathReplacementPost p g ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementMap (p ≫ g) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementMap p ≫ g := by
  change comparisonPathReplacementPost p g ≫
    pullback.fst (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint D 0) (p ≫ g) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint D 1 = _
  rw [← Category.assoc, comparisonPathReplacementPost_path, Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathMap_endpoint, ← Category.assoc]
  rfl

/-- 概要：Kan 複体の path 置換の全空間の後合成の比較は同値。
方針：元の源への二つの自明 Kan fibration とその可換式で二対三則を使う。
規約：この全空間の射には g の同値性を要求しない。
使われ方：底 g の同値性と合わせて各導来 fiber の比較を得る。 -/
lemma comparisonPathReplacementPost_homotopyEquivalence {E B D : SSet.{u}}
    [KanComplex E] [KanComplex B] [KanComplex D] (p : E ⟶ B) (g : B ⟶ D) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (comparisonPathReplacementPost p g) := by
  have h₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementProjection p) :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.isQCatEquivalence_of_trivialKanFibration _).isSimplicialHomotopyEquivalence
  have h₂ : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementProjection (p ≫ g)) :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.isQCatEquivalence_of_trivialKanFibration _).isSimplicialHomotopyEquivalence
  apply h₂.cancel_right
  rw [comparisonPathReplacementPost_source]
  exact h₁

/-- 概要：標的への後合成が元の比較射の導来 fiber に誘導する実際の射。
方針：path 置換の可換正方形を頂点 fiber の射へ移す。
規約：固定する頂点 b を g(b) へ移す。
使われ方：錐の切断模型の同値による導来 fiber の標的の変更。 -/
def comparisonFiberPost {E B D : SSet.{u}} (p : E ⟶ B) (g : B ⟶ D) (b : B _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.comparisonFiber p b ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.comparisonFiber (p ≫ g) (g.app _ b) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.vertexFiberSquareMap (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementMap p) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementMap (p ≫ g))
    (comparisonPathReplacementPost p g) g (comparisonPathReplacementPost_target p g).symm b

/-- 概要：導来 fiber の後合成の比較は path 置換への包含と可換。
方針：頂点 fiber の正方形の比較の包含の式を使う。
規約：全空間の射は構成済みの path の後合成。
使われ方：導来 fiber の二つの成分の計算。 -/
lemma comparisonFiberPost_ι {E B D : SSet.{u}} (p : E ⟶ B) (g : B ⟶ D) (b : B _⦋0⦌) :
    comparisonFiberPost p g b ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementMap (p ≫ g)) (g.app _ b) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementMap p) b ≫ comparisonPathReplacementPost p g :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.vertexFiberSquareMap_ι _ _ _ _ _ _

/-- 概要：導来 fiber の後合成の比較は源成分を保つ。
方針：包含の可換式と path 置換の源射影の可換式を合成する。
規約：元の始域への厳密な射の等式。
使われ方：元の比較射の源を保持する比較 span の検証。 -/
lemma comparisonFiberPost_source {E B D : SSet.{u}} (p : E ⟶ B) (g : B ⟶ D) (b : B _⦋0⦌) :
    comparisonFiberPost p g b ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.comparisonFiberSource (p ≫ g) (g.app _ b) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.comparisonFiberSource p b := by
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.comparisonFiberSource, ← Category.assoc, comparisonFiberPost_ι]
  rw [Category.assoc, comparisonPathReplacementPost_source]

/-- 概要：導来 fiber の後合成の比較は path 成分に g を後合成する。
方針：包含の可換式と path 置換の第一射影の計算を合成する。
規約：源成分の変更とは区別する。
使われ方：導来 fiber の実際の比較射の path の座標。 -/
lemma comparisonFiberPost_path {E B D : SSet.{u}} (p : E ⟶ B) (g : B ⟶ D) (b : B _⦋0⦌) :
    comparisonFiberPost p g b ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.comparisonFiberPath (p ≫ g) (g.app _ b) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.comparisonFiberPath p b ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathMap g := by
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.comparisonFiberPath, ← Category.assoc, comparisonFiberPost_ι]
  rw [Category.assoc, comparisonPathReplacementPost_path, ← Category.assoc]

/-- 概要：Kan 複体間の標的の比較が同値なら実際の導来 fiber の後合成の比較射も同値。
方針：path 置換の全空間の同値と底の同値を任意の fiber の実際の比較へ渡す。
規約：元の射 p の fibration 性も、元の始域や fiber の非空性も要求しない。
使われ方：元の q_x の導来 fiber を同値な切断模型の fiber へ移す。 -/
lemma comparisonFiberPost_homotopyEquivalence {E B D : SSet.{u}}
    [KanComplex E] [KanComplex B] [KanComplex D] (p : E ⟶ B) (g : B ⟶ D)
    (hg : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence g) (b : B _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (comparisonFiberPost p g b) := by
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.vertexFiberSquareMap_homotopyEquivalence _ _ _ _ _
    (comparisonPathReplacementPost_homotopyEquivalence p g) hg b

end
end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces
