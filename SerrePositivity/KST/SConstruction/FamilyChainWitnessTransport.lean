module
public import SerrePositivity.KST.SConstruction.FamilyChainWitnessPrecomposition
public import SerrePositivity.KST.SConstruction.FamilyCompositeImageClasses

/-! # 元の全合成木の端点表示の移送
概要：元の合成木を端点の表示等号に沿って移し、元の全二単体を厳密に保持する。
方針：端点の表示等号で帰納し、元の同じ全木を保持する。
規約：元の全区間・全三角形を選び直さず、同じ元の合成木を保持する。
使われ方：二入力側と単一合成射側の元の直接補正を共通の全列へ合わせる。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial

/-- 端点の表示だけを移し、元の同じ全合成木を保持する。 -/
def familyChainWitnessEndpointTransport {U E : SSet.{u}} {f g f' g' : U ⟶ E}
    {c : FamilyHomotopyChain f g} {H : SSet.Homotopy f g}
    (w : FamilyChainCompositionWitness c H) (hs : f' = f) (ht : g = g') :
    FamilyChainCompositionWitness
      (familyHomotopyChainSourceTransport (familyHomotopyChainTargetTransport c ht) hs)
      (familyHomotopyEndpointTransport H hs ht) := by
  cases hs
  cases ht
  exact w

/-- 端点の表示移送でも、元の同じ全合成三角形を同じ順序で保持する。 -/
lemma familyChainWitnessEndpointTransport_triangles {U E : SSet.{u}} {f g f' g' : U ⟶ E}
    {c : FamilyHomotopyChain f g} {H : SSet.Homotopy f g}
    (w : FamilyChainCompositionWitness c H) (hs : f' = f) (ht : g = g') :
    familyChainCompositionTriangles (familyChainWitnessEndpointTransport w hs ht) =
      familyChainCompositionTriangles w := by
  cases hs
  cases ht
  rfl

end SerrePositivity.KST.SConstruction
