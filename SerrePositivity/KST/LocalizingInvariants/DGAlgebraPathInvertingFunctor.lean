module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPathFunctor

/-!
概要：準同型を反転する実関手は、元の乗法的経路の両端を等しい射に送る。
方針：経路の対角の可逆性と両評価の切断式から、両評価の像を同定する。
規約：一般の導来写像空間比較は仮定しない。使われ方：有限 Postnikov の pro 比較。
-/

@[expose] public section
noncomputable section
universe u v w
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
variable (R : Type u) [CommRing R] {C : Type v} [Category.{w} C]
  (L : Mon (Complex R) ⥤ C)

/-- 元の代数射の準同型を反転する、通常圏への関手。 -/
def InvertsQuasiIsos : Prop :=
  ∀ {A B : Mon (Complex R)} (f : A ⟶ B), QuasiIso f.hom → IsIso (L.map f)

/-- connective 代数の間の準同型だけを反転する条件。 -/
def InvertsConnectiveQuasiIsos : Prop :=
  ∀ {A B : Mon (Complex R)}, IsConnective R A → IsConnective R B →
    ∀ (f : A ⟶ B), QuasiIso f.hom → IsIso (L.map f)

lemma InvertsQuasiIsos.connective (hL : InvertsQuasiIsos R L) :
    InvertsConnectiveQuasiIsos R L := fun _ _ f hf => hL f hf

lemma Path.Witness.map_eq_of_diagonalIso {A B : Mon (Complex R)} {a b : A ⟶ B}
    (h : Path.Witness R a b) [IsIso (L.map (Path.diagonal R B))] : L.map a = L.map b := by
  have he : L.map (Path.source R B) = L.map (Path.target R B) := by
    apply (cancel_epi (L.map (Path.diagonal R B))).1
    rw [← L.map_comp, ← L.map_comp, Path.diagonal_source, Path.diagonal_target]
  calc
    L.map a = L.map (h.hom ≫ Path.source R B) := congrArg L.map h.source_eq.symm
    _ = L.map (h.hom ≫ Path.target R B) := by rw [L.map_comp, L.map_comp, he]
    _ = L.map b := congrArg L.map h.target_eq

lemma Path.Witness.map_eq {A B : Mon (Complex R)} {a b : A ⟶ B}
    (hL : InvertsQuasiIsos R L) (h : Path.Witness R a b) : L.map a = L.map b := by
  have := hL (Path.diagonal R B) (Path.diagonal_quasiIso R B)
  exact h.map_eq_of_diagonalIso R L

lemma Path.Witness.map_eq_of_connective {A B : Mon (Complex R)} {a b : A ⟶ B}
    (hL : InvertsConnectiveQuasiIsos R L) (hB : IsConnective R B)
    (h : Path.Witness R a b) : L.map a = L.map b := by
  have := hL hB (Path.isConnective hB) (Path.diagonal R B) (Path.diagonal_quasiIso R B)
  exact h.map_eq_of_diagonalIso R L

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
