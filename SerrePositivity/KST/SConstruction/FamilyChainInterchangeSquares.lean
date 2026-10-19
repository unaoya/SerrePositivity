module
public import SerrePositivity.KST.SConstruction.FamilyInterchangeSquares

/-! # 補正有限列の全区間と元の適合円柱の交換
概要：補正列の各実区間に対する区間交換正方形を、四面と共に順序付きで保存する。
方針：元の trace の各円柱へ、同じ第二円柱との二時刻の構成を適用する。
規約：全区間の順序・四辺・パラメータの制限を保持する。
使われ方：K 合成補正の射影 trace と元の適合区間を照合する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
variable {U E F G : SSet.{u}} {a b : U ⟶ E}
  (c : FamilyHomotopyChain a b) (k : U ⊗ (Δ[1] : SSet.{u}) ⟶ F) (m : E ⊗ F ⟶ G)

/-- 元の補正列の各区間と同じ適合円柱との実交換正方形列。 -/
def familyHomotopyChainInterchangeSquares :
    List ((U ⊗ (Δ[1] : SSet.{u})) ⊗ (Δ[1] : SSet.{u}) ⟶ G) :=
  (familyHomotopyChainTrace c).map (fun h => familyInterchangeSquare h k m)

/-- 第二時刻の零面は、元の全補正区間と適合円柱の始点の合成列。 -/
lemma familyHomotopyChainInterchangeSquares_second_zero :
    (familyHomotopyChainInterchangeSquares c k m).map (SSet.ι₀ ≫ ·) =
      (familyHomotopyChainTrace c).map (fun h => lift h (fst U Δ[1] ≫ SSet.ι₀ ≫ k) ≫ m) := by
  simp only [familyHomotopyChainInterchangeSquares, List.map_map, Function.comp_def,
    familyInterchangeSquare_second_zero]

/-- 第二時刻の一面は、元の全補正区間と適合円柱の終点の合成列。 -/
lemma familyHomotopyChainInterchangeSquares_second_one :
    (familyHomotopyChainInterchangeSquares c k m).map (SSet.ι₁ ≫ ·) =
      (familyHomotopyChainTrace c).map (fun h => lift h (fst U Δ[1] ≫ SSet.ι₁ ≫ k) ≫ m) := by
  simp only [familyHomotopyChainInterchangeSquares, List.map_map, Function.comp_def,
    familyInterchangeSquare_second_one]

/-- 第一時刻の零面は、元の各始点と同じ適合円柱との合成列。 -/
lemma familyHomotopyChainInterchangeSquares_first_zero :
    (familyHomotopyChainInterchangeSquares c k m).map ((SSet.ι₀ (X := U) ▷ Δ[1]) ≫ ·) =
      (familyHomotopyChainTrace c).map (fun h => lift (fst U Δ[1] ≫ SSet.ι₀ ≫ h) k ≫ m) := by
  simp only [familyHomotopyChainInterchangeSquares, List.map_map, Function.comp_def,
    familyInterchangeSquare_first_zero]

/-- 第一時刻の一面は、元の各終点と同じ適合円柱との合成列。 -/
lemma familyHomotopyChainInterchangeSquares_first_one :
    (familyHomotopyChainInterchangeSquares c k m).map ((SSet.ι₁ (X := U) ▷ Δ[1]) ≫ ·) =
      (familyHomotopyChainTrace c).map (fun h => lift (fst U Δ[1] ≫ SSet.ι₁ ≫ h) k ≫ m) := by
  simp only [familyHomotopyChainInterchangeSquares, List.map_map, Function.comp_def,
    familyInterchangeSquare_first_one]

/-- 全正方形の制限は、元の補正全区間と同じ適合円柱の制限からの構成に一致する。 -/
lemma familyHomotopyChainInterchangeSquares_restrict {T : SSet.{u}} (j : T ⟶ U) :
    (familyHomotopyChainInterchangeSquares c k m).map
      (((j ▷ (Δ[1] : SSet.{u})) ▷ (Δ[1] : SSet.{u})) ≫ ·) =
      familyHomotopyChainInterchangeSquares (familyHomotopyChainPrecomp j c)
        ((j ▷ (Δ[1] : SSet.{u})) ≫ k) m := by
  simp only [familyHomotopyChainInterchangeSquares, familyHomotopyChainPrecomp_trace,
    List.map_map, Function.comp_def, familyInterchangeSquare_restrict]

end SerrePositivity.KST.SConstruction
