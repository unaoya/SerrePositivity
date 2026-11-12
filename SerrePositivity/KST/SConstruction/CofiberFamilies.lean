module
public import SerrePositivity.KST.SConstruction.CofiberCompletionLifting

/-! # cofiber の族とその選択空間
概要：任意の図式の族に cofiber を coherent に選び、既存部分を固定できる。
方針：入力への trivial Kan fibration と内部 Hom の可縮な fiber を用いる。
規約：追加の cofiber 公理は導入しない。使われ方：gapped 図式の復元と加法性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 概要：cofiber の族を既存部分の選択を保って延長できる。
方針：cofiber の射影の単射に対する持ち上げを使う。
規約：パラメーターに quasicategory 性・有限性は要求しない。
使われ方：第一行からの cofiber 補完の相対段階。 -/
lemma exists_relative_cofiberFamily {A B C : SSet.{u}} [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable C]
    (i : A ⟶ B) [Mono i] (d : B ⟶ (ihom (Δ[1] : SSet.{u})).obj C)
    (a : A ⟶ cofiberDiagrams C) (ha : a ≫ cofiberProjection C = i ≫ d) :
    ∃ F : B ⟶ cofiberDiagrams C, i ≫ F = a ∧ F ≫ cofiberProjection C = d := by
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration.mem (p := cofiberProjection C) i inferInstance
  have sq : CommSq a i (cofiberProjection C) d := ⟨ha⟩
  exact ⟨sq.lift, sq.fac_left, sq.fac_right⟩

/-- 概要：同じ入力の族に対する cofiber の全選択の空間。
方針：内部 Hom の後合成の指定頂点上の fiber を取る。
規約：単なる選択の集合ではなく高次比較を含む単体集合。
使われ方：cofiber の選択の可縮性。 -/
def cofiberFamilySpace {A C : SSet.{u}} (d : A ⟶ (ihom (Δ[1] : SSet.{u})).obj C) : SSet.{u} :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber ((ihom A).map (cofiberProjection C)) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex d)

/-- 概要：cofiber の族の全選択空間は可縮な Kan 複体。
方針：trivial Kan fibration は内部 Hom で保たれ、その fiber は可縮。
規約：A は任意の単体集合。使われ方：第一行復元のパラメーター付きの一意性。 -/
lemma cofiberFamilySpace_isContractibleKan {A C : SSet.{u}} [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable C]
    (d : A ⟶ (ihom (Δ[1] : SSet.{u})).obj C) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan (cofiberFamilySpace d) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_isContractibleKan ((ihom A).map (cofiberProjection C)) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex d)

/-- 概要：同じ入力の族の二つの cofiber の選択は関手として同型。
方針：同じ基底へ写る二つの持ち上げを可縮な fiber 内で比較する。
規約：全パラメーターに自然な比較。使われ方：cofiber の選択によらない構成。 -/
def cofiberFamiliesIso {A C : SSet.{u}} [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable C]
    (d : A ⟶ (ihom (Δ[1] : SSet.{u})).obj C) (F G : A ⟶ cofiberDiagrams C)
    (hF : F ≫ cofiberProjection C = d) (hG : G ≫ cofiberProjection C = d) : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso F G :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorIsoOfTrivialKanFibration (cofiberProjection C) F G (hF.trans hG.symm)

/-- 概要：全ての射に cofiber 四角形を関手的に選ぶ切断。
方針：入力への trivial Kan fibration の厳密な切断を取る。
規約：この一つの選択に証明は依存しない。使われ方：cofiber 関手の具体的な表示。 -/
def cofiberSection (C : SSet.{u}) [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable C] :
    (ihom (Δ[1] : SSet.{u})).obj C ⟶ cofiberDiagrams C :=
  Classical.choose (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.trivialKanFibration_exists_section (cofiberProjection C))

/-- 概要：選んだ cofiber の入力は厳密に元の射。
方針：切断の選択の仕様を使う。
規約：ホモトピー等号に弱めない。使われ方：cofiber の境界の回収。 -/
lemma cofiberSection_projection (C : SSet.{u}) [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable C] :
    cofiberSection C ≫ cofiberProjection C = 𝟙 _ :=
  Classical.choose_spec (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.trivialKanFibration_exists_section (cofiberProjection C))

/-- 概要：射の cofiber 頂点を取る関手。
方針：選んだ普遍四角形を (1,1) の角で評価する。
規約：実際の単体集合の射。使われ方：S• の復元と反復構成。 -/
def cofiberFunctor (C : SSet.{u}) [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable C] :
    (ihom (Δ[1] : SSet.{u})).obj C ⟶ C :=
  cofiberSection C ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ IsCofiberDiagramVertex).ι ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (1 : Fin 2), stdSimplex.obj₀Equiv.symm (1 : Fin 2))

end SerrePositivity.KST.SConstruction
