module

public import SerrePositivity.InfinityCategories.HA.Monads.WalkingAdjunctionOrdinalWidthVertices
public import SerrePositivity.InfinityCategories.HA.Monads.FiniteFunctorObjects

/-!
概要：重みを有限範囲に制限した全実鎖の全体は有限である。
方針：重みの対象の単射性と実射の有限順序表示の忠実性を一般の関手の有限性へ渡す。
規約：元の実関手そのものを数え、同型類へ落とさない。
使われ方：Riehl–Verity Proposition 4.2.15の各幅での有限性、HA Proposition 4.7.3.3、
Kerodon Remark 6.2.1.4（Tag 02EN）の前の実filtrationの有限な範囲。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory

namespace SerrePositivity.InfinityCategories.HA.Monads

/-- 概要：四つのwalking Homの二対象間の元の実射は有限個。
方針：実射の忠実な有限単調射の表示を有限関数型へ単射で入れる。
規約：元の全実射の有限性。使われ方：Riehl–Verity §4.2の実全鎖の有限性。 -/
lemma walkingAdjunctionHom_finite (X Y : WalkingAdjunctionPoint) (A B : walkingAdjunctionHom X Y) :
    Finite (A ⟶ B) := by
  apply Finite.of_injective (fun f : A ⟶ B => fun i => walkingAdjunctionOrderHom f i)
  intro f g h
  apply walkingAdjunctionOrderHom_injective
  apply OrderHom.ext
  funext i
  exact congrFun h i

/-- 概要：重みが指定値以下の実対象は有限個。
方針：重みの有限値に単射で入れる。規約：四Homの実対象そのもの。
使われ方：Riehl–Verity §4.2の各幅での実頂点の有限性。 -/
lemma walkingAdjunctionBoundedObjects_finite (X Y : WalkingAdjunctionPoint) (w : ℕ) :
    Finite {A : walkingAdjunctionHom X Y // walkingAdjunctionWeight X Y A ≤ w} := by
  apply Finite.of_injective (fun A : {A : walkingAdjunctionHom X Y //
      walkingAdjunctionWeight X Y A ≤ w} =>
    (⟨walkingAdjunctionWeight X Y A.val, Nat.lt_succ_of_le A.property⟩ : Fin (w + 1)))
  intro A B h
  apply Subtype.ext
  apply walkingAdjunctionWeight_injective X Y
  exact congrArg Fin.val h

/-- 概要：全頂点の重みが指定値以下の実全鎖は、固定次数で有限個。
方針：実対象と実Homの有限性を、対象ごとに範囲を制限した関手の有限性へ渡す。
規約：全実射の作用を含む。使われ方：Riehl–Verity §4.2の各幅での実原子の有限性。 -/
lemma walkingAdjunctionBoundedChains_finite (n : ℕ) (X Y : WalkingAdjunctionPoint) (w : ℕ) :
    Finite {H : ComposableArrows (walkingAdjunctionHom X Y) n //
      ∀ i, walkingAdjunctionWeight X Y (H.obj i) ≤ w} := by
  let : Finite {A : walkingAdjunctionHom X Y // walkingAdjunctionWeight X Y A ≤ w} :=
    walkingAdjunctionBoundedObjects_finite X Y w
  let : ∀ A B : walkingAdjunctionHom X Y, Finite (A ⟶ B) :=
    walkingAdjunctionHom_finite X Y
  exact finite_functors_of_objectwise_finite (fun A => walkingAdjunctionWeight X Y A ≤ w)

end SerrePositivity.InfinityCategories.HA.Monads
