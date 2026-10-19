module
public import SerrePositivity.KST.SConstruction.FamilyInterchangeSquares

/-! # 区間交換正方形を実円柱間の補正列として保持する
概要：元の補正列と固定円柱の交換を、円柱そのものを対象とする実ホモトピー有限列に束ねる。
方針：独立な二時刻の役割を交換して、元の各正方形を円柱間の実ホモトピーとして使う。
規約：全正方形とその順序を保存し、成分の等式へ忘れない。
使われ方：元の合成適合円柱を補正済み BF 合成の適合円柱へ運ぶ二次元補正。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
variable {U E F G : SSet.{u}}

/-- 元の円柱を固定し、他方の実ホモトピーで円柱自体を動かす二次元ホモトピー。 -/
def familyInterchangeCylinderHomotopy {a b : U ⟶ E} (H : SSet.Homotopy a b)
    (k : U ⊗ (Δ[1] : SSet.{u}) ⟶ F) (m : E ⊗ F ⟶ G) :
    SSet.Homotopy (lift (fst U Δ[1] ≫ a) k ≫ m) (lift (fst U Δ[1] ≫ b) k ≫ m) where
  h := familyInterchangeSquare k H.h ((β_ F E).hom ≫ m)
  h₀ := by
    change SSet.ι₀ ≫ familyInterchangeSquare k H.h ((β_ F E).hom ≫ m) = _
    rw [familyInterchangeSquare_second_zero, H.h₀, ← Category.assoc]
    congr 1
  h₁ := by
    change SSet.ι₁ ≫ familyInterchangeSquare k H.h ((β_ F E).hom ≫ m) = _
    rw [familyInterchangeSquare_second_one, H.h₁, ← Category.assoc]
    congr 1
  rel := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro x
    exact False.elim x.1.property

/-- 元の全正方形を使い、元の円柱の始点側から終点側へ実二次元補正列を作る。 -/
def familyInterchangeCylinderChain {a b : U ⟶ E} (c : FamilyHomotopyChain a b)
    (k : U ⊗ (Δ[1] : SSet.{u}) ⟶ F) (m : E ⊗ F ⟶ G) :
    FamilyHomotopyChain (lift (fst U Δ[1] ≫ a) k ≫ m) (lift (fst U Δ[1] ≫ b) k ≫ m) := by
  induction c with
  | nil => exact .nil _
  | cons H tail ih => exact .cons (familyInterchangeCylinderHomotopy H k m) ih

/-- 二次元補正列は、元の各区間と固定円柱からの実正方形だけを順に保持する。 -/
lemma familyInterchangeCylinderChain_trace {a b : U ⟶ E} (c : FamilyHomotopyChain a b)
    (k : U ⊗ (Δ[1] : SSet.{u}) ⟶ F) (m : E ⊗ F ⟶ G) :
    familyHomotopyChainTrace (familyInterchangeCylinderChain c k m) =
      (familyHomotopyChainTrace c).map
        (fun h => familyInterchangeSquare k h ((β_ F E).hom ≫ m)) := by
  induction c with
  | nil => rfl
  | cons H tail ih =>
      change familyInterchangeSquare k H.h ((β_ F E).hom ≫ m) ::
        familyHomotopyChainTrace (familyInterchangeCylinderChain tail k m) = _
      rw [ih]
      rfl

end SerrePositivity.KST.SConstruction
