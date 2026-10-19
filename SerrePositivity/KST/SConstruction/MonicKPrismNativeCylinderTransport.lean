module
public import SerrePositivity.KST.SConstruction.MonicKPrismNativeSecondTraceFace

/-! # 元の全三角形の第二面から保存済み補正円柱への実二次元列
概要：元の第二面を始点に、保存済みの後続適合円柱の補正全区間を引き戻す。
方針：元の二入力パラメータへの射対で全正方形を制限し、始点の表示だけを移す。
規約：全補正区間と順序を保持し、零段には区間を追加しない。
使われ方：元の合成適合三角形を、補正済み BF 合成の射影 trace へ接続する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet Spectra
open scoped Simplicial
variable {I : Type u} [SmallCategory I] (F : I ⥤ StableModel.{u})
  {x y z : I} (f : x ⟶ y) (g : y ⟶ z)

/-- 元の全三角形の第二面を、同じ全正方形列で補正済みの後続適合円柱へ運ぶ。 -/
def monicKPrismNativeSecondCompatibilityTransport (n : ℕ) : FamilyHomotopyChain
    ((nerve (CompositionStringParameters f g) ◁ stdSimplex.δ 0) ≫
      monicKPrismCompositionNativeTriangle n F f g)
    ((compositionStringPair f g ▷ (Δ[1] : SSet.{u})) ≫
      monicKPrismCompositeSecondCompatibility F f g n) :=
  familyHomotopyChainSourceTransport
    (familyHomotopyChainPrecomp (compositionStringPair f g ▷ (Δ[1] : SSet.{u}))
      (monicKPrismCompositeSecondCompatibilityTransport F f g n))
    (monicKPrismCompositionNativeTriangle_second_trace n F f g)

/-- 二次元補正列の全 trace は、元の各交換正方形の同じパラメータ制限。 -/
lemma monicKPrismNativeSecondCompatibilityTransport_trace (n : ℕ) :
    familyHomotopyChainTrace (monicKPrismNativeSecondCompatibilityTransport F f g n) =
      (familyHomotopyChainTrace (monicKPrismCompositeSecondCompatibilityTransport F f g n)).map
        (((compositionStringPair f g ▷ (Δ[1] : SSet.{u})) ▷ (Δ[1] : SSet.{u})) ≫ ·) := by
  rw [monicKPrismNativeSecondCompatibilityTransport, familyHomotopyChainSourceTransport_trace,
    familyHomotopyChainPrecomp_trace]
  rfl

/-- 零段の実二次元補正には区間がない。 -/
lemma monicKPrismNativeSecondCompatibilityTransport_zero_trace :
    familyHomotopyChainTrace (monicKPrismNativeSecondCompatibilityTransport F f g 0) = [] := by
  rw [monicKPrismNativeSecondCompatibilityTransport_trace,
    monicKPrismCompositeSecondCompatibilityTransport_zero_trace, List.map_nil]

/-- 零段では、元の全第二面は補正後の同じ適合円柱そのものである。 -/
lemma monicKPrismCompositionNativeTriangle_second_zero :
    (nerve (CompositionStringParameters f g) ◁ stdSimplex.δ 0) ≫
        monicKPrismCompositionNativeTriangle 0 F f g =
      (compositionStringPair f g ▷ (Δ[1] : SSet.{u})) ≫
        monicKPrismCompositeSecondCompatibility F f g 0 :=
  familyHomotopyChain_eq_of_trace_nil (monicKPrismNativeSecondCompatibilityTransport F f g 0)
    (monicKPrismNativeSecondCompatibilityTransport_zero_trace F f g)

end SerrePositivity.KST.SConstruction
