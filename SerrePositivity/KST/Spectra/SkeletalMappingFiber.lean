module

public import SerrePositivity.KST.Spectra.UnbasedMappingFiberIso

/-!
概要：骨格の点つき写像空間の塔の各 fiber の相対 cofiber による表示。
方針：隣り合う骨格の包含へ制限射の fiber 同型を適用する。
規約：段 n から n+1 へ追加する単体の次元は n+1。
使われ方：Goerss–Jardine VIII §1。塔の fiber と群 cochain の比較の準備。
-/

@[expose] public section

universe u

open CategoryTheory SSet Opposite HomotopicalAlgebra
open SSet.modelCategoryQuillen

namespace SerrePositivity.KST.Spectra.UnbasedPointedMapping

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：骨格の塔の隣り合う段の包含。
方針：骨格の単調性を部分複体の射にする。
規約：n 骨格から n+1 骨格への射。
使われ方：Goerss–Jardine VIII §1。fiber の源の相対商の入力。 -/
def skeletalInclusion (K : SSet.{u}) (n : ℕ) :
    (K.skeleton (n + 1) : SSet.{u}) ⟶ (K.skeleton (n + 1 + 1) : SSet.{u}) :=
  Subcomplex.homOfLE (K.skeleton.monotone (Nat.le_succ (n + 1)))

/-- 概要：骨格の隣り合う段の相対 cofiber。
方針：骨格の包含に自由基点を加えて相対商を取る。
規約：元の低い骨格全体を基点へ潰す。
使われ方：Goerss–Jardine VIII §1。塔の fiber の写像空間の源。 -/
def skeletalRelativeSource (K : SSet.{u}) (n : ℕ) : PointedSimplicialSet.{u} :=
  relativeSource (skeletalInclusion K n)

/-- 概要：骨格の写像空間の塔の隣接遷移の基点 fiber。
方針：点つき塔の実際の遷移へ pointedFiber を適用する。
規約：射は高い骨格からの写像空間から低い骨格からの写像空間へ向かう。
使われ方：Goerss–Jardine VIII §1。塔のホモトピー長完全列の fiber。 -/
def stageFiber (K : SSet.{u}) (X : PointedSimplicialSet.{u}) (n : ℕ) :
    PointedSimplicialSet.{u} :=
  pointedFiber ((tower K X).map (homOfLE (Nat.le_succ n)).op)

instance stageFiber_kanComplex (K : SSet.{u}) (X : PointedSimplicialSet.{u})
    [KanComplex X.right] (n : ℕ) : KanComplex (stageFiber K X n).right := by
  let := tower_map_fibration K X (homOfLE (Nat.le_succ n)).op
  exact pointedFiber_kanComplex _

/-- 概要：塔の各 fiber は相対骨格からの点つき Hom と同型。
方針：隣接骨格の包含へ制限射の相対 cofiber 表示を適用する。
規約：係数の Kan 性は同型自体には不要。
使われ方：Goerss–Jardine VIII §1。各 fiber の群をセルで計算する界面。 -/
def stageFiberIso (K : SSet.{u}) (X : PointedSimplicialSet.{u}) (n : ℕ) :
    PointedObject.basedHom (skeletalRelativeSource K n) X ≅ stageFiber K X n :=
  restrictionFiberIso (skeletalInclusion K n) X

/-- 概要：相対骨格の Hom の正次数の群は塔の fiber の正次数の群と同型。
方針：点つき fiber の厳密な同型を Kan ホモトピー群へ送る。
規約：r は実際のホモトピー次数 r+1。セルによる次数移動はまだ含まない。
使われ方：Goerss–Jardine I §7、VIII §1。fiber の群を相対骨格へ移す界面。 -/
def stageFiberHomotopyEquiv (K : SSet.{u}) (X : PointedSimplicialSet.{u})
    [KanComplex X.right] (n r : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (PointedObject.basedHom (skeletalRelativeSource K n) X).right r
        (PointedSimplicialSet.basepoint (PointedObject.basedHom (skeletalRelativeSource K n) X)) ≃*
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (stageFiber K X n).right r (stageFiber K X n).basepoint := by
  let e : (PointedObject.basedHom (skeletalRelativeSource K n) X).right ≅
      (stageFiber K X n).right := PointedSimplicialSet.forget.mapIso (stageFiberIso K X n)
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.equivOfIso r e
    (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint (stageFiberIso K X n).hom)

end

end SerrePositivity.KST.Spectra.UnbasedPointedMapping
