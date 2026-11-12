module

public import SerrePositivity.KST.Spectra.KanSequenceMappingParameter
public import SerrePositivity.KST.Spectra.TwistedKanSequenceParameter
public import SerrePositivity.KST.Spectra.SignedLoopSequence

/-!
概要：元の全列のパラメータ族に、符号付き loop 列の作用を厳密に施す。
方針：mapping の作用とパラメータ交換を、同じ反転との可換性で twist し、一段移動する。
規約：段ごとの族から列射を推論しない。使われ方：源の StrictInterval の実評価側への移送。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalClosed
namespace SerrePositivity.KST.Spectra.KanSequence

/-- 元のパラメータ付き列射を、同じパラメータを持つ符号付き loop 列の族へ移す。 -/
def signedLoopParameterHom {A : PointedSimplicialSet.{u}} {X Y : KanSequence.{u}}
    (f : Hom X (mapping A Y)) : Hom (signedLoopTail X) (mapping A (signedLoopTail Y)) := by
  let q := mappingParameterHom CirclePower.space.{u} f
  let r := mappingPre (CirclePower.integerPowerMap.{u} (-1)) X
  let s := mappingPre (CirclePower.integerPowerMap.{u} (-1)) Y
  have h (n : ℕ) : r.app n ≫ q.app n = q.app n ≫ (ihom A).map (s.app n) := by
    exact congrArg (fun p => p.app n)
      (mappingParameterHom_pre (CirclePower.integerPowerMap.{u} (-1)) f)
  exact tailHom (twistParameterHom r s q h)

/-- 符号付き全列作用の各段は、元の次段族の mapping と同じパラメータ交換。 -/
lemma signedLoopParameterHom_app {A : PointedSimplicialSet.{u}} {X Y : KanSequence.{u}}
    (f : Hom X (mapping A Y)) (n : ℕ) :
    (signedLoopParameterHom f).app n = (ihom CirclePower.space.{u}).map (f.app (n + 1)) ≫
      (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso CirclePower.space.{u} A (Y.level (n + 1)).space).hom := rfl

end SerrePositivity.KST.Spectra.KanSequence
