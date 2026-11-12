module
public import SerrePositivity.KST.SConstruction.Cofinality.MultiCompletion
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TerminalVertices

/-!
概要：同じ全多次数の S 図式で wide 部分圏に入る旗の全関手部分圏を構成する。
方針：wide 部分複体への旗が与える頂点で ambient 関手圏の全部分複体を取る。
規約：旗間の射は ambient の全射を保持し、wide 部分圏自身の内部 Hom と混同しない。
使われ方：Sp-7 の部分複体を入力とする相対 S• の旗方向。
-/

@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction.Cofinality
open CategoryTheory MonoidalClosed SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

variable (r : ℕ) (ι : Fin r → SimplexCategoryᵒᵖ) (Y : StableModel.{u})

/-- 概要：同じ S 多次数内で指定部分複体へ入る旗の頂点条件。
方針：旗全体の厳密な持ち上げを存在量化する。
規約：辺ごとの独立な選択や頂点だけの所属条件へ弱めない。
使われ方：相対旗の全関手部分圏の定義。 -/
def multiRelativeFlagPredicate
    (M : (((multiSEndofunctor r).obj ι).obj Y).carrier.Subcomplex) (K : SSet.{u})
    (v : ((ihom K).obj (((multiSEndofunctor r).obj ι).obj Y).carrier) _⦋0⦌) : Prop :=
  ∃ g : K ⟶ (M : SSet.{u}), _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (g ≫ M.ι) = v

/-- 概要：同じ S 多次数の相対旗の全高次単体を保持する。
方針：持ち上がる旗を頂点とする ambient 関手圏の全部分複体。
規約：M は wide 部分圏の供給値を受け取り、この定義に閉性の公理を追加しない。
使われ方：相対 S• の旗方向の各段。 -/
def multiRelativeFlags
    (M : (((multiSEndofunctor r).obj ι).obj Y).carrier.Subcomplex) (K : SSet.{u}) :
    SSet.{u} :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices ((ihom K).obj (((multiSEndofunctor r).obj ι).obj Y).carrier)
    (multiRelativeFlagPredicate r ι Y M K)

instance multiRelativeFlags_quasicategory
    (M : (((multiSEndofunctor r).obj ι).obj Y).carrier.Subcomplex) (K : SSet.{u}) :
    Quasicategory (multiRelativeFlags r ι Y M K) := by
  unfold multiRelativeFlags
  infer_instance

/-- 概要：相対旗から元の同じ多次数の全旗への包含。
方針：定義した全部分複体の包含を使う。
規約：標的は元の反復 S 上の関手圏。
使われ方：元の未置換 S 図式との照合。 -/
def multiRelativeFlagsInclusion
    (M : (((multiSEndofunctor r).obj ι).obj Y).carrier.Subcomplex) (K : SSet.{u}) :
    multiRelativeFlags r ι Y M K ⟶
      (ihom K).obj (((multiSEndofunctor r).obj ι).obj Y).carrier :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ (multiRelativeFlagPredicate r ι Y M K)).ι

/-- 概要：旗の任意の前合成は相対旗を同じ多次数内に保つ。
方針：元の旗全体の持ち上げをそのまま前合成する。
規約：境界や面を新しく選ばず、指定された射を使う。
使われ方：相対旗方向の面・退化の実作用。 -/
def multiRelativeFlagsPrecomp
    (M : (((multiSEndofunctor r).obj ι).obj Y).carrier.Subcomplex)
    {L K : SSet.{u}} (i : L ⟶ K) :
    multiRelativeFlags r ι Y M K ⟶ multiRelativeFlags r ι Y M L :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift (multiRelativeFlagPredicate r ι Y M L)
    (multiRelativeFlagsInclusion r ι Y M K ≫
      (pre i).app (((multiSEndofunctor r).obj ι).obj Y).carrier) (by
        intro v
        obtain ⟨g, hg⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices_vertex v
        refine ⟨i ≫ g, ?_⟩
        change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex ((i ≫ g) ≫ M.ι) =
          ((pre i).app _).app (Opposite.op ⦋0⦌) v.val
        exact (congrArg (fun q => ((pre i).app _).app (Opposite.op ⦋0⦌) q) hg))

/-- 概要：相対旗の前合成は包含後に元の ambient 前合成と厳密に一致。
方針：全部分複体への持ち上げの包含公式。
規約：同型だけの比較に弱めない。
使われ方：全多単体構造の自然性検査。 -/
lemma multiRelativeFlagsPrecomp_inclusion
    (M : (((multiSEndofunctor r).obj ι).obj Y).carrier.Subcomplex)
    {L K : SSet.{u}} (i : L ⟶ K) :
    multiRelativeFlagsPrecomp r ι Y M i ≫ multiRelativeFlagsInclusion r ι Y M L =
      multiRelativeFlagsInclusion r ι Y M K ≫
        (pre i).app (((multiSEndofunctor r).obj ι).obj Y).carrier := rfl

end SerrePositivity.KST.SConstruction.Cofinality
