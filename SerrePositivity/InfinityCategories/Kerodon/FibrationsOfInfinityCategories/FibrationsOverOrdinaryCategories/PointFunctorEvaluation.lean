module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.RelativeFunctorEvaluation

/-!
概要：一点からの関手空間の評価による厳密な同型。
方針：評価の逆を第二射影の curry で作り、標準零単体の各次数の一意性で往復を示す。
規約：quasicategory 性と Kan 性は要求しない。
使われ方：Kerodon §5.3.1（Tag 035D）、相対関手の一点への制限と元の fiber の同定。

対応節は Kerodon 5.3（Tag 035A）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories

/-- 概要：curry した図式を頂点で評価すると元の図式のその頂点での制限。
方針：各次数で評価と curry を計算し、恒等写像の作用を消去する。
規約：頂点とパラメータは任意。
使われ方：Kerodon §4.5.1（Tag 01DQ）、§5.3.1（Tag 035D）、相対評価の逆射の計算。 -/
lemma curry_evaluateFunctorAt_vertex {A T E : SSet.{u}} (H : A ⊗ T ⟶ E) (v : A _⦋0⦌) :
    curry H ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt v = lift (SSet.const v) (𝟙 T) ≫ H := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro t
  change H.app (Opposite.op ⦋n⦌)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant v n, T.map (𝟙 (Opposite.op ⦋n⦌)) t) = _
  rw [CategoryTheory.Functor.map_id_apply]
  rfl

/-- 概要：標準零単体の任意の次数の単体は唯一の頂点の定値単体。
方針：全頂点の値が零であることを有限型の値で確認する。
規約：任意の次数 n を扱う。
使われ方：Kerodon §5.3.1（Tag 035D）、一点からの関手の評価の単射性。 -/
lemma stdSimplex_zero_eq_constant {n : ℕ} (b : (Δ[0] : SSet.{u}) _⦋n⦌) :
    b = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (stdSimplex.obj₀Equiv.symm 0) n := by
  apply stdSimplex.ext
  intro i
  apply Fin.ext
  change (b i).val = 0
  have hb := (b i).isLt
  omega

/-- 概要：一点からの関手単体集合の評価は元の単体集合への厳密な同型。
方針：第二射影を curry して逆を作り、零単体の成分の一意性で往復を計算する。
規約：標準零単体の唯一の頂点で評価する。
使われ方：Kerodon §5.3.1（Tag 035D）、strict transport の始対象への制限の値の回収。 -/
def pointFunctorEvaluationIso (E : SSet.{u}) : (ihom (Δ[0] : SSet.{u})).obj E ≅ E where
  hom := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm 0)
  inv := curry (snd (Δ[0] : SSet.{u}) E)
  hom_inv_id := by
    apply uncurry_injective
    rw [uncurry_natural_left, uncurry_curry]
    apply SSet.hom_ext
    rintro ⟨⟨n⟩⟩
    apply ConcreteCategory.hom_ext
    rintro ⟨b, F⟩
    change F.app (Opposite.op ⦋n⦌) (𝟙 _) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (stdSimplex.obj₀Equiv.symm 0) n) =
      F.app (Opposite.op ⦋n⦌) (𝟙 _) b
    rw [stdSimplex_zero_eq_constant b]
  inv_hom_id := by
    rw [curry_evaluateFunctorAt_vertex, lift_snd]

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
