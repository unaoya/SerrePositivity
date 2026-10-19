module
public import SerrePositivity.KST.SConstruction.KSuspensionSpecifiedPasting
public import SerrePositivity.KST.SConstruction.MonicKPrismCompatibility

/-! # 元の単射置換を保つ全貼り合わせの実適合辺
概要：全貼り合わせの適合辺を元の単射置換の射影に沿って移し、既存の指定辺を厳密に回収する。
方針：一般の列の射に沿う適合辺の前合成を使い、指定頂点で元の辺の等式を移す。
規約：元の構造射と既存の単射置換の射影を固定し、新しいホモトピー代表を選ばない。
使われ方：元の K square の全貼り合わせ選択から、BF の相対厳密化に使う実円柱への接続。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet
open Spectra Spectra.PointedMapping
open scoped Simplicial

/-- 任意の貼り合わせ辺を、元の射影で単射置換した源へそのまま前合成する。 -/
def monicKSpanPastingEdge {I : Type u} [SmallCategory I]
    (r : ℕ) (F : I ⥤ StableModel.{u}) {i j : I} (f : i ⟶ j)
    (v : (kKanSuspensionPastingChoices r F f) _⦋0⦌) :=
  sequenceCompatibilityEdge_precompose (monicKKanSequenceProjection (F.obj i))
    (kKanSequenceLevelMap (F.map f)) r (kKanSuspensionPastingEdge r F f v)

/-- 元の指定頂点では、BF の厳密化に用いている同じ単射源の適合辺を回収する。 -/
lemma monicKSpanPastingEdge_specified {I : Type u} [SmallCategory I]
    (r : ℕ) (F : I ⥤ StableModel.{u}) {i j : I} (f : i ⟶ j) :
    monicKSpanPastingEdge r F f (kKanSuspensionSpecifiedPastingVertex r F f) =
      monicKPrismCompatibilityEdge r F f :=
  congrArg (sequenceCompatibilityEdge_precompose (monicKKanSequenceProjection (F.obj i))
    (kKanSequenceLevelMap (F.map f)) r) (kKanSuspensionPastingEdge_specified r F f)

/-- 任意の貼り合わせの単射源での実基点固定適合ホモトピー。 -/
def monicKSpanPastingHomotopy {I : Type u} [SmallCategory I]
    (r : ℕ) (F : I ⥤ StableModel.{u}) {i j : I} (f : i ⟶ j)
    (v : (kKanSuspensionPastingChoices r F f) _⦋0⦌) : SSet.Homotopy
      (((monicKKanSequence (F.obj i)).sigma r ≫
        monicKToRawLevelMap (F.map f) (r + 1)).right)
      ((PointedSimplicialSet.circle.{u} ◁ monicKToRawLevelMap (F.map f) r ≫
        (kKanSequence (F.obj j)).sigma r).right) :=
  homotopyOfEdge (monicKSpanPastingEdge r F f v)

/-- 元の指定頂点では、既存の単射源の適合ホモトピーの実円柱そのものを回収する。 -/
lemma monicKSpanPastingHomotopy_specified {I : Type u} [SmallCategory I]
    (r : ℕ) (F : I ⥤ StableModel.{u}) {i j : I} (f : i ⟶ j) :
    (monicKSpanPastingHomotopy r F f (kKanSuspensionSpecifiedPastingVertex r F f)).h =
      (monicKPrismCompatibilityHomotopy r F f).h := by
  rw [monicKSpanPastingHomotopy, monicKSpanPastingEdge_specified]
  rfl

end SerrePositivity.KST.SConstruction
