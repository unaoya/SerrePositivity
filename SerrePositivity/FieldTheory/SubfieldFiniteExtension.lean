module

public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.RingTheory.AlgebraTower
public import Mathlib.RingTheory.Finiteness.Basic

/-! # 有限体拡大の部分体上の有限性

E⊆K、K→L、Eの像⊆G⊆Lなら、K/EとL/Kの有限性からL/Gの有限性を得る。
合成写像による作用とGの部分体としての作用を、同じスカラー塔で確認する。
-/

@[expose] public noncomputable section
namespace SerrePositivity
variable {K L : Type*} [Field K] [Field L] [Algebra K L]

/-- 共有限な部分体の像を含む、有限拡大内の部分体も共有限。 -/
theorem finite_subfield_of_map_le
    (E : Subfield K) (G : Subfield L) (hEG : E.map (algebraMap K L) ≤ G)
    [Module.Finite E K] [Module.Finite K L] : Module.Finite G L := by
  let f : E →+* L := (algebraMap K L).comp E.subtype
  let : Algebra E L := f.toAlgebra
  let : Module E L := @Algebra.toModule _ _ _ _ (inferInstance : Algebra E L)
  let : SMul E L := (inferInstance : Algebra E L).toSMul
  let : IsScalarTower E K L := IsScalarTower.of_algebraMap_eq' (R := E) (S := K) (A := L) rfl
  let : Module.Finite E L := Module.Finite.trans (R := E) K L
  let g : E →+* G := f.codRestrict G (fun c ↦ hEG (Subfield.mem_map.mpr ⟨c, c.property, rfl⟩))
  let : Algebra E G := g.toAlgebra
  let : IsScalarTower E G L := IsScalarTower.of_algebraMap_eq' (R := E) (S := G) (A := L) rfl
  exact Module.Finite.of_restrictScalars_finite E G L

end SerrePositivity
