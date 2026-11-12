module
public import SerrePositivity.KST.SConstruction.STrivialFibration
public import SerrePositivity.KST.SConstruction.MultiRealization
public import SerrePositivity.HomotopicalAlgebra.Simplicial.DiagonalLocalizedEquivalence

/-! # 有限反復 S の trivial Kan fibration の保存
概要：有限反復 S は各多次数で自明ファイブレーションを保ち、core の実現後に弱同値を与える。
方針：反復方向数について帰納し、各段の S の持ち上げ性を適用する。
規約：入力の射は安定な入力の圏の射。使われ方：経路比較の反復への移送。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet
open SerrePositivity.InfinityCategories SerrePositivity.SimplicialModel

/-- 概要：有限反復の自己関手は底の自明ファイブレーションを保つ。
方針：内側の反復で得た自明ファイブレーションに、外側の S の保存を適用する。
規約：全ての多次数で成立。使われ方：自然な経路比較の反復。
-/
instance multiSEndofunctor_map_trivialKanFibration (r : ℕ) {X Y : StableModel.{u}}
    (p : X ⟶ Y) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration p.val] (d : Fin r → SimplexCategoryᵒᵖ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration ((((multiSEndofunctor r).obj d).map p).val) := by
  induction r with
  | zero => exact inferInstanceAs (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration p.val)
  | succ r ih =>
    let q := ((multiSEndofunctor r).obj (fun i => d i.succ)).map p
    let : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration q.val := ih (fun i => d i.succ)
    change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (sPostcompCofiber (d 0).unop.len q.val q.property)
    infer_instance

/-- 概要：有限反復の core の射は各多次数で自明ファイブレーション。
方針：反復の底の射の充填性を core に制限する。
規約：源と標的の quasicategory 性は反復の構成から得る。使われ方：対角の比較。 -/
instance multiCoreSConstructionFunctor_map_trivialKanFibration (r : ℕ)
    {X Y : StableModel.{u}} (p : X ⟶ Y) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration p.val]
    (d : Fin r → SimplexCategoryᵒᵖ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (((multiCoreSConstructionFunctor r).map p).app d) := by
  exact coreMap_trivialKanFibration ((((multiSEndofunctor r).obj d).map p).val)

/-- 概要：有限反復 S の core の対角実現は自明ファイブレーションを弱同値へ写す。
方針：対角添字に制限した各段の充填性と対角の局所化比較を使う。
規約：対角自身の Kan 性は不要。使われ方：反復の弱同値比較。 -/
lemma multiRealizationFunctor_map_localized_isIso (r : ℕ) {X Y : StableModel.{u}}
    (p : X ⟶ Y) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration p.val] :
    IsIso (AnodyneHomotopy.anodyneQ.map ((multiRealizationFunctor r).map p)) := by
  let α := Functor.whiskerLeft (multiIndexDiagonal r) ((multiCoreSConstructionFunctor r).map p)
  have hi (d : SimplexCategoryᵒᵖ) : IsIso (AnodyneHomotopy.anodyneQ.map (α.app d)) := by
    let : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (α.app d) :=
      multiCoreSConstructionFunctor_map_trivialKanFibration r p ((multiIndexDiagonal r).obj d)
    exact map_isIso_of_trivialKanFibration AnodyneHomotopy.anodyneQ
      (Localization.inverts AnodyneHomotopy.anodyneQ SSet.anodyneExtensions) _
  exact SerrePositivity.BisimplicialModel.localized_diagonal_map α hi

end SerrePositivity.KST.SConstruction
