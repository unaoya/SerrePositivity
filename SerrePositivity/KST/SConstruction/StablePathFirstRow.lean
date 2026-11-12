module
public import SerrePositivity.KST.SConstruction.PathFirstRowNaturality
public import SerrePositivity.KST.SConstruction.FunctorCofiberPreservation
public import SerrePositivity.KST.SConstruction.SOneExact

/-! # 安定な入力の圏における経路の第一行比較
概要：経路と第一行の図式を安定な入力の圏の図式に束ねる。
方針：関手圏の安定性と添字制限の cofiber 保存を使う。
規約：底の図式は既存の全 gapped 経路。使われ方：有限反復 S の適用。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 概要：安定な入力の圏に値を持つ S の経路図式。
方針：単体的 S 自己関手を入力で評価してから経路構成を取る。
規約：第 n 段は元の S_(n+1)。使われ方：経路の反復 S の源。 -/
def stableSPathDiagram (X : StableModel.{u}) : SimplicialObject StableModel.{u} :=
  simplicialPath (simplicialStableEndofunctor ⋙
    (evaluation StableModel.{u} StableModel.{u}).obj X)

/-- 概要：第一行の関手圏を安定な入力として束ねた単体的図式。
方針：関手圏の安定性と、添字制限の零対象・cofiber の保存を使う。
規約：第 n 段は Fun(N([n]),X)。使われ方：経路の反復 S の標的。 -/
def stablePathFirstRowDiagram (X : StableModel.{u}) : SimplicialObject StableModel.{u} where
  obj d := {
    carrier := (pathFirstRowDiagram X.carrier).obj d
    quasicategory := inferInstance
    stable := by
      change _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable ((ihom (firstRowNerve (d.unop.len + 1))).obj X.carrier)
      infer_instance }
  map f := ⟨(pathFirstRowDiagram X.carrier).map f, by
    change PreservesCofiberData ((pre (pathFirstRowNerveFunctor.map f.unop)).app X.carrier)
    exact ⟨fun _ hz => functor_reindex_isZeroVertex _ hz,
      fun t ht => functor_reindex_preserves_cofiber _ t ht⟩⟩
  map_id d := Subtype.ext ((pathFirstRowDiagram X.carrier).map_id d)
  map_comp f g := Subtype.ext ((pathFirstRowDiagram X.carrier).map_comp f g)

/-- 概要：安定な入力の圏に束ねた経路の第一行制限。
方針：各段の第一行制限が零対象と全押し出しを保つことを使う。
規約：自然性は底の元の自然変換と同じ。使われ方：有限反復へ写す比較射。 -/
def stablePathFirstRowRestriction (X : StableModel.{u}) :
    stableSPathDiagram X ⟶ stablePathFirstRowDiagram X where
  app d := ⟨(pathFirstRowRestriction X.carrier).app d,
    (firstRowRestriction_preservesSConstructionData (d.unop.len + 1) X.carrier).toCofiberData⟩
  naturality {_d _e} f := Subtype.ext ((pathFirstRowRestriction X.carrier).naturality f)

/-- 概要：束ねた第一行制限の底の射は各段で自明ファイブレーション。
方針：元の第一行制限の充填性を使う。
規約：全単体次数で成立。使われ方：反復による充填性の保存の入力。 -/
instance stablePathFirstRowRestriction_trivialKanFibration (X : StableModel.{u})
    (d : SimplexCategoryᵒᵖ) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (((stablePathFirstRowRestriction X).app d).val) :=
  firstRowRestriction_trivialKanFibration _ X.carrier

/-- 概要：安定な入力の圏へ束ねた比較を忘れると元の第一行の自然変換になる。
方針：各段の保存条件だけを忘れる。
規約：厳密等号。使われ方：元の図式との照合。 -/
lemma stablePathFirstRowRestriction_forget (X : StableModel.{u}) :
    Functor.whiskerRight (stablePathFirstRowRestriction X) stableModelForget =
      pathFirstRowRestriction X.carrier := rfl

/-- 概要：第一行の零次の関手圏から元の安定な入力への比較。
方針：一点の内部 Hom の同型に、自明ファイブレーションの保存条件を付ける。
規約：底は既存の firstRowOneHomNatIso。使われ方：既存の S₁ 比較との安定な入力での照合。 -/
def stablePathFirstRowZeroComparison (X : StableModel.{u}) :
    (stablePathFirstRowDiagram X).obj (Opposite.op ⦋0⦌) ⟶ X :=
  ⟨firstRowOneHomNatIso.hom.app X.carrier,
    (preservesSConstructionData_of_trivialKanFibration _).toCofiberData⟩

/-- 概要：束ねた経路の零次比較の合成は既存の stable S₁ 比較。
方針：底の零次比較の厳密な式を保存条件付きの射へ移す。
規約：厳密等号。使われ方：有限反復の一次方向との照合。 -/
lemma stablePathFirstRowRestriction_zero (X : StableModel.{u}) :
    (stablePathFirstRowRestriction X).app (Opposite.op ⦋0⦌) ≫
      stablePathFirstRowZeroComparison X = stableSOneComparison X := Subtype.ext rfl

end SerrePositivity.KST.SConstruction
