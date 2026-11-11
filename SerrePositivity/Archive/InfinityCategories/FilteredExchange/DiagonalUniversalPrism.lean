module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.DiagonalFiberTransport

/-!
概要：元の全区間の普遍輸送族を、元の動く初期値と区間で制限した実 prism を公開する。
方針：元の普遍輸送族の実 prism をそのまま使い、実両端・射影・再制限を計算する。
規約：輸送を再選択しない。使われ方：元の長辺比較の第二の実 prism の照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {P E B : SSet.{u}} (p : E ⟶ B) [LeftFibration p] {a b : B _⦋0⦌}
  (f : P ⟶ vertexFiber p a) (c : P ⟶ intervalMappingSpace a b)

/-- 元の全区間の普遍輸送を、元の同じ初期値と区間で制限した実 prism。 -/
def diagonalUniversalPrism : (Δ[1] : SSet.{u}) ⊗ P ⟶ E :=
  (Δ[1] ◁ lift f c) ≫ (parametrizedFiberTransportFamily p a b).prism

/-- 元の実普遍 prism の始点は、元の同じ動く初期値。 -/
lemma diagonalUniversalPrism_start :
    prismEndpoint 0 P ≫ diagonalUniversalPrism p f c = f ≫ vertexFiberι p a := by
  rw [diagonalUniversalPrism, ← Category.assoc, prismEndpoint_naturality, Category.assoc,
    (parametrizedFiberTransportFamily p a b).start,
    ← Category.assoc, ← Category.assoc]
  change (lift f c ≫ fst _ _) ≫ (𝟙 _ ≫ vertexFiberι p a) = _
  rw [lift_fst, Category.id_comp]

/-- 元の実普遍 prism の終点は、元の同じ対角輸送。 -/
lemma diagonalUniversalPrism_finish :
    prismEndpoint 1 P ≫ diagonalUniversalPrism p f c =
      diagonalFiberTransport p f c ≫ vertexFiberι p b := by
  rw [diagonalUniversalPrism, ← Category.assoc, prismEndpoint_naturality, Category.assoc,
    (parametrizedFiberTransportFamily p a b).finish]
  exact (Category.assoc _ _ _).symm

/-- 元の実普遍 prism は、元の同じ動く区間を被覆する。 -/
lemma diagonalUniversalPrism_projection :
    diagonalUniversalPrism p f c ≫ p = intervalMappingUncurry c := by
  rw [diagonalUniversalPrism, Category.assoc,
    (parametrizedFiberTransportFamily p a b).over_base,
    ← whiskerLeft_comp_assoc, lift_snd, ← intervalMappingUncurry_precomp, Category.comp_id]

/-- 元の実普遍 prism の全係数の再制限は、元の初期値と区間の同じ再制限。 -/
lemma diagonalUniversalPrism_precomp {Q : SSet.{u}} (r : Q ⟶ P) :
    (Δ[1] ◁ r) ≫ diagonalUniversalPrism p f c =
      diagonalUniversalPrism p (r ≫ f) (r ≫ c) := by
  rw [diagonalUniversalPrism, ← Category.assoc, ← whiskerLeft_comp, comp_lift]
  rfl

end SerrePositivity.InfinityCategories.F2
