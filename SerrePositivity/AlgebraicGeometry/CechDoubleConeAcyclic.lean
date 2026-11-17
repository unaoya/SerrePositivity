module

public import SerrePositivity.AlgebraicGeometry.CechDoubleConeSwap
public import SerrePositivity.AlgebraicGeometry.CechConeQuasiIsoAcyclic

/-!
概要：可換四角の二つの辺の cone の完全性を、cone の比較の cone に移す。
方針：二重 cone を交換し、完全な二複体の間の射の準同型性を使う。
規約：元の四角形の実際の余鎖写像と可換性を保持する。
使われ方：共通細分での四角形の増大全複体の比較。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory
universe u v
variable {R : Type v} [CommRing R]
variable {A B A' B' : CochainComplex (ModuleCat.{u} R) ℕ}

/-- 二辺の cone が完全な可換四角は、cone の比較の cone も完全。 -/
theorem cechRefinementConeMap_cone_acyclic
    (f : A ⟶ B) (g : A' ⟶ B') (a : A ⟶ A') (b : B ⟶ B')
    (h : f ≫ b = a ≫ g)
    (ha : (cechRefinementCone A A' a).Acyclic)
    (hb : (cechRefinementCone B B' b).Acyclic) :
    (cechRefinementCone (cechRefinementCone A B f) (cechRefinementCone A' B' g)
      (cechRefinementConeMap a b h)).Acyclic := by
  have he := cechRefinementCone_acyclic_of_quasiIso
    (cechRefinementCone A A' a) (cechRefinementCone B B' b)
    (cechRefinementConeMap f g h.symm)
    (fun q ↦ (quasiIsoAt_iff_exactAt _ q (ha q)).mpr (hb q))
  let e := cechDoubleConeSwapIso f g a b h
  intro q
  exact (exactAt_iff_of_quasiIsoAt e.hom q).mpr (he q)

end SerrePositivity.AlgebraicGeometry
