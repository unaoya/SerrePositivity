module

public import SerrePositivity.KST.NonConnective.SequentialLevelColimit
public import Mathlib.CategoryTheory.Types.Monomorphisms

/-!
概要：逐次 BF 射の相対置換に用いる点つき押し出しの単射性。
方針：基点忘却が押し出しを保存することと単体集合の単射の cobase-change 安定性を使う。
規約：対象に Kan 性は要求しない。
使われ方：元の構造射を保つ相対 cofibrant 置換。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.KST.NonConnective

/-- 点つき押し出しの左注入は、反対の辺の単射性を保つ。 -/
lemma sequentialPointedPushout_inl_mono {A B C : PointedSimplicialSet.{u}}
    (f : A ⟶ B) (g : A ⟶ C) [Mono g.right] :
    Mono (pushout.inl f g).right := by
  let h := (IsPushout.of_hasPushout f g).map PointedSimplicialSet.forget
  exact MorphismProperty.of_isPushout (P := MorphismProperty.monomorphisms SSet.{u})
    h (inferInstanceAs (Mono g.right))

end SerrePositivity.KST.NonConnective
