module

public import SerrePositivity.AlgebraicGeometry.CechAlgebraEqualizerMap
public import SerrePositivity.AlgebraicGeometry.ProjectiveCechNonemptyComparison

/-!
概要：非空交叉で自然な代数同型から適合切断代数の同型を作る。
方針：長さ一と二のタプルだけを使い、各成分の同型で適合条件を移す。
規約：空交叉の係数の比較は要求しない。
使われ方：斉次局所化と実際の Proj の構造層の切断代数の比較。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory
universe u
variable {R : Type u} [CommRing R] {ι : Type} [DecidableEq ι]
variable {D E : Finset ι ⥤ CommAlgCat.{u} R}
variable (e : ∀ T : Finset ι, T.Nonempty → D.obj T ≃ₐ[R] E.obj T)
variable (he : ∀ {T U : Finset ι} (hT : T.Nonempty) (h : T ⊆ U) (x : D.obj T),
  e U (hT.mono h) ((D.map (homOfLE h)).hom x) =
    (E.map (homOfLE h)).hom (e T hT x))

/-- 非空交叉の比較を長さ q+1 の切断族に適用する代数同型。 -/
def fullAlgebraCechNonemptyCochainsEquiv (q : ℕ) :
    FullRingCechCochains (algebraCechRingDiagram D) (q + 1) ≃ₐ[R]
      FullRingCechCochains (algebraCechRingDiagram E) (q + 1) where
  toFun a t := e _ (cechTupleSupport_nonempty t) (a t)
  invFun a t := (e _ (cechTupleSupport_nonempty t)).symm (a t)
  left_inv a := by funext t; exact (e _ _).symm_apply_apply (a t)
  right_inv a := by funext t; exact (e _ _).apply_symm_apply (a t)
  map_mul' a b := by funext t; exact map_mul _ _ _
  map_add' a b := by funext t; exact map_add _ _ _
  commutes' r := by funext t; exact (e _ _).commutes r

include he in
/-- 切断族の比較は二つの面と可換。 -/
theorem fullAlgebraCechNonemptyCochainsEquiv_face (i : Fin 2)
    (a : FullRingCechCochains (algebraCechRingDiagram D) 1) :
    fullAlgebraCechNonemptyCochainsEquiv e 1 (fullAlgebraCechFace D i a) =
      fullAlgebraCechFace E i (fullAlgebraCechNonemptyCochainsEquiv e 0 a) := by
  funext t
  exact he (cechTupleSupport_nonempty (t ∘ i.succAbove))
    (cechTupleSupport_face_subset t i) (a (t ∘ i.succAbove))

include he in
/-- 非空交叉の比較は適合条件を保ち、かつ反映する。 -/
theorem fullAlgebraCechNonemptyCochainsEquiv_mem_iff
    (a : FullRingCechCochains (algebraCechRingDiagram D) 1) :
    fullAlgebraCechNonemptyCochainsEquiv e 0 a ∈ fullAlgebraCechEqualizer E ↔
      a ∈ fullAlgebraCechEqualizer D := by
  change (fullAlgebraCechFace E 0 _ = fullAlgebraCechFace E 1 _) ↔
    (fullAlgebraCechFace D 0 a = fullAlgebraCechFace D 1 a)
  rw [← fullAlgebraCechNonemptyCochainsEquiv_face e he,
    ← fullAlgebraCechNonemptyCochainsEquiv_face e he]
  exact (fullAlgebraCechNonemptyCochainsEquiv e 1).injective.eq_iff

/-- 非空交叉だけの自然な比較から得られる適合切断の代数同型。 -/
def fullAlgebraCechNonemptyEqualizerEquiv :
    fullAlgebraCechEqualizer D ≃ₐ[R] fullAlgebraCechEqualizer E where
  toFun a := ⟨fullAlgebraCechNonemptyCochainsEquiv e 0 a.val,
    (fullAlgebraCechNonemptyCochainsEquiv_mem_iff e he a.val).mpr a.property⟩
  invFun a := ⟨(fullAlgebraCechNonemptyCochainsEquiv e 0).symm a.val, by
    apply (fullAlgebraCechNonemptyCochainsEquiv_mem_iff e he _).mp
    rw [AlgEquiv.apply_symm_apply]
    exact a.property⟩
  left_inv a := Subtype.ext ((fullAlgebraCechNonemptyCochainsEquiv e 0).symm_apply_apply a.val)
  right_inv a := Subtype.ext ((fullAlgebraCechNonemptyCochainsEquiv e 0).apply_symm_apply a.val)
  map_mul' a b := Subtype.ext (map_mul _ _ _)
  map_add' a b := Subtype.ext (map_add _ _ _)
  commutes' r := Subtype.ext ((fullAlgebraCechNonemptyCochainsEquiv e 0).commutes r)

/-- 適合切断の同型は、各成分で指定された代数同型を適用する。 -/
theorem fullAlgebraCechNonemptyEqualizerEquiv_apply
    (a : fullAlgebraCechEqualizer D) (t : Fin 1 → ι) :
    (fullAlgebraCechNonemptyEqualizerEquiv e he a).val t =
      e _ (cechTupleSupport_nonempty t) (a.val t) := rfl

end SerrePositivity.AlgebraicGeometry
