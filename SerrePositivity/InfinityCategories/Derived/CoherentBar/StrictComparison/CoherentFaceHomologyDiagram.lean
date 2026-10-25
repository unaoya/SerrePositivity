module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.CoherentPrefixHomologyDiagram
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.CoherentFaceBlockHomology

/-!
概要：正の番号の面のホモロジー係数は H(G) の同じ始点係数の恒等射である。
方針：端点の等号射の自然性と実面ブロックの shift 比較を合成する。
規約：等号輸送を保持してから係数の恒等性を導く。
使われ方：非退化ホモロジー bar の正の面との比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded DGNerve SSet
open scoped Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  {J : Type u} [PartialOrder J]
  (G : (SSet.uliftFunctor.{max (u + 1) v, u}).obj (nerve J) ⟶
    dgNerve R (RightModule R D))

lemma dgCoherentBarVertexHomologyTransport_eq (x : D) (r : ℤ)
    {M N : RightModule R D} (hMN : M = N) (j : J)
    (hM : M = coherentDiagramVertex G (nerveEquiv.symm j))
    (hN : N = coherentDiagramVertex G (nerveEquiv.symm j)) :
    HomologicalComplex.homologyMap ((moduleEvaluation R D x).map
      (eqToHom (congrArg (ForgetEnrichment.of (Complex R)) hMN))) r ≫
      (dgCoherentBarVertexHomologyTransportIso R D G x r N j hN).hom =
    (dgCoherentBarVertexHomologyTransportIso R D G x r M j hM).hom := by
  cases hMN
  simp only [eqToHom_refl, CategoryTheory.Functor.map_id, HomologicalComplex.homologyMap_id,
    Category.id_comp]

lemma dgCoherentBarSignedFaceHomologyDiagram {n : ℕ} (s : (nerve J) _⦋n + 1⦌)
    (i : Fin (n + 1)) (x : D) (q : ℤ) :
    dgDegreeOneHomologyMap R (dgCoherentBarSignedFaceCochain R D G s i x)
      (dgCoherentBarSignedFaceCochain_closed R D G s i x) q ≫
      (dgComplexShiftHomologyIso R
        ((dgCoherentBarSource R D G (dgCoherentBarFace s i.succ)).obj (Opposite.op x))
        (n : ℤ) (q + 1) (q + ((n : ℤ) + 1)) (by omega)).hom ≫
      (dgCoherentBarVertexHomologyTransportIso R D G x (q + ((n : ℤ) + 1))
        (dgCoherentBarSource R D G (dgCoherentBarFace s i.succ)) (s.obj 0)
        ((dgCoherentBarSource_face_succ R D G s i).trans
          (dgCoherentBarSource_nerve R D G (n + 1) s))).hom =
    (dgComplexShiftHomologyIso R
      ((dgCoherentBarSource R D G ⟨n + 1, s⟩).obj (Opposite.op x))
      ((n : ℤ) + 1) q (q + ((n : ℤ) + 1)) (by omega)).hom ≫
        (dgCoherentBarSourceHomologyIso R D G x (q + ((n : ℤ) + 1)) (n + 1) s).hom := by
  rw [← Category.assoc, dgCoherentBarSignedFaceHomology, Category.assoc,
    dgCoherentBarVertexHomologyTransport_eq R D G x (q + ((n : ℤ) + 1))
      (dgCoherentBarSource_face_succ R D G s i).symm (s.obj 0)
      (dgCoherentBarSource_nerve R D G (n + 1) s)
      ((dgCoherentBarSource_face_succ R D G s i).trans
        (dgCoherentBarSource_nerve R D G (n + 1) s))]
  rfl

end SerrePositivity.InfinityCategories
