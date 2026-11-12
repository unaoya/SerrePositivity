module
public import SerrePositivity.KST.ProExcision.DiscreteActionNaturality

/-!
# 群の準同型の零次ホモトピー

概要：群の分類空間の一つの頂点を使い、任意の群準同型から自明射への零次比較を構成する。
方針：入力射の定数区間写像を使い、零次の両端を一致させる。
規約：KST Definition A.3、Construction A.5、Lemma 4.16 の帰納法の基底。
使われ方：A.5 の第二因子の0次入力および Lemma 4.16 の m=0。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.KST.ProExcision
open CategoryTheory Opposite
open scoped Simplicial
variable {T H : Type u} [Group T] [Group H]

/-- 概要：二つの群準同型の自由化は零次で一致する。
方針：零次の nerve と一対象圏の対象の同値の単射性を使う。
規約：KST A.3・4.16、非被約零次を含む。
使われ方：定数区間による0次比較の終点の一致。 -/
lemma groupLinearizedMap_zero_eq (f g : T →* H) :
    (groupLinearizedMap f).app (op ⦋0⦌) = (groupLinearizedMap g).app (op ⦋0⦌) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerLinearization_hom_ext
  intro x
  change _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerLinearization.map ((nerveMap (SingleObj.mapHom _ _ f)).app (op ⦋0⦌))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerGenerator x) = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerLinearization.map
      ((nerveMap (SingleObj.mapHom _ _ g)).app (op ⦋0⦌)) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerGenerator x)
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerLinearization_map_generator, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerLinearization_map_generator]
  apply congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerGenerator
  apply nerveEquiv.injective
  rfl

/-- 概要：群準同型の自由化と自明射の自由化の実0次ホモトピー。
方針：入力射の定数区間を取り、唯一の頂点による零次一致を使う。
規約：KST A.5 の0次入力、Lemma 4.16 の帰納基底。
使われ方：非可換な群 Q の恒等写像にも適用する。 -/
def groupZeroMHomotopy (f : T →* H) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.LinearizedMHomotopy (groupLinearizedMap f) (groupLinearizedMap (1 : T →* H)) 0 where
  h := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedCylinderProjection (nerve (SingleObj T)) ≫ groupLinearizedMap f
  h₀ n hn := by
    have h : n = 0 := Nat.eq_zero_of_le_zero hn
    subst n
    simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedEndpoint₀_projection_assoc]
  h₁ n hn := by
    have h : n = 0 := Nat.eq_zero_of_le_zero hn
    subst n
    simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedEndpoint₁_projection_assoc] using groupLinearizedMap_zero_eq f (1 : T →* H)

/-- 概要：同変な群準同型の標準0次ホモトピーは同変。
方針：同変な射から作る定数区間の同変性を使う。
規約：KST A.5・4.16、外部 G は一般のモノイドでよい。
使われ方：帰納法の基底と第二因子の0次入力。 -/
lemma groupZeroMHomotopy_equivariant {G : Type u} [Monoid G]
    (ρT : G →* Monoid.End T) (ρH : G →* Monoid.End H) (f : T →* H)
    (hf : ∀ a t, f (ρT a t) = ρH a (f t)) :
    LinearizedCylinderEquivariant (discreteNerveAction (MonCat.of G) (MonCat.of T) ρT)
      (discreteNerveAction (MonCat.of G) (MonCat.of H) ρH) (groupZeroMHomotopy f).h :=
  (groupLinearizedMap_equivariant ρT ρH f hf).constant

end SerrePositivity.KST.ProExcision
