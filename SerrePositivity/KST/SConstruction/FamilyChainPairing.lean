module
public import SerrePositivity.KST.SConstruction.FamilyHomotopyChains

/-! # 固定した族と補正全区間の積
概要：一方の族を固定してもう一方の全補正区間を積へ移す。
方針：各実円柱と時間に定数な固定族を積の普遍性で組にする。
規約：区間の順序と全時刻の射を保存する。
使われ方：二本の入力射の BF 族の合成に現れる補正列。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial

/-- 一方の族を全時刻で固定した積の実ホモトピー。 -/
def familyHomotopyPairLeft {U A B : SSet.{u}} (a : U ⟶ A) {b c : U ⟶ B}
    (H : SSet.Homotopy b c) : SSet.Homotopy (lift a b) (lift a c) where
  h := lift (fst U (Δ[1] : SSet.{u}) ≫ a) H.h
  h₀ := by
    change SSet.ι₀ ≫ lift (fst U (Δ[1] : SSet.{u}) ≫ a) H.h = lift a b
    apply CartesianMonoidalCategory.hom_ext
    · rw [Category.assoc, lift_fst, lift_fst, ← Category.assoc, SSet.ι₀_fst, Category.id_comp]
    · rw [Category.assoc, lift_snd, lift_snd, H.h₀]
  h₁ := by
    change SSet.ι₁ ≫ lift (fst U (Δ[1] : SSet.{u}) ≫ a) H.h = lift a c
    apply CartesianMonoidalCategory.hom_ext
    · rw [Category.assoc, lift_fst, lift_fst, ← Category.assoc, SSet.ι₁_fst, Category.id_comp]
    · rw [Category.assoc, lift_snd, lift_snd, H.h₁]
  rel := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro x
    exact False.elim x.1.property

/-- 固定した族と、元の補正有限列の積。 -/
def familyHomotopyChainPairLeft {U A B : SSet.{u}} (a : U ⟶ A) {b c : U ⟶ B}
    (d : FamilyHomotopyChain b c) : FamilyHomotopyChain (lift a b) (lift a c) := by
  induction d with
  | nil => exact .nil _
  | cons H tail ih => exact .cons (familyHomotopyPairLeft a H) ih

/-- 積の補正列の全区間は、固定族と元の各実円柱の組そのものである。 -/
lemma familyHomotopyChainPairLeft_trace {U A B : SSet.{u}} (a : U ⟶ A) {b c : U ⟶ B}
    (d : FamilyHomotopyChain b c) :
    familyHomotopyChainTrace (familyHomotopyChainPairLeft a d) =
      (familyHomotopyChainTrace d).map (fun h => lift (fst U (Δ[1] : SSet.{u}) ≫ a) h) := by
  induction d with
  | nil => rfl
  | cons H tail ih =>
      change lift (fst U (Δ[1] : SSet.{u}) ≫ a) H.h ::
        familyHomotopyChainTrace (familyHomotopyChainPairLeft a tail) = _
      rw [ih]
      rfl

end SerrePositivity.KST.SConstruction
