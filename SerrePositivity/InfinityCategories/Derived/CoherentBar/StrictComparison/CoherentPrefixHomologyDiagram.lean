module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.CoherentVertexHomologyTransport

/-!
概要：一次 prefix の実ホモロジー係数を H(G) の関手の辺へ同定する。
方針：閉零加群射の等号から頂点ホモロジーの自然性を使い、shift 比較へ合成する。
規約：元の coherent 図式と実 prefix 係数を保持する。
使われ方：非退化 bar の零番の面との微分比較。
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

def dgCoherentBarSourceHomologyIso (x : D) (r : ℤ) (n : ℕ) (s : (nerve J) _⦋n⦌) :
    ((dgCoherentBarSource R D G ⟨n, s⟩).obj (Opposite.op x)).homology r ≅
      (dgCoherentBarHomologyDiagram R D G x r).obj (s.obj 0) :=
  dgCoherentBarVertexHomologyTransportIso R D G x r (dgCoherentBarSource R D G ⟨n, s⟩)
    (s.obj 0) (dgCoherentBarSource_nerve R D G n s)

lemma dgCoherentBarPrefixHomologyDiagram_naturality {n : ℕ} (s : (nerve J) _⦋n + 1⦌)
    (x : D) (r : ℤ) :
    HomologicalComplex.homologyMap ((moduleEvaluation R D x).map
      (moduleMorphismOfCycle R D
        (M := ForgetEnrichment.of (Complex R) (dgCoherentBarSource R D G ⟨n + 1, s⟩))
        (N := ForgetEnrichment.of (Complex R)
          (dgCoherentBarSource R D G (dgCoherentBarTail s 1 (by omega))))
        (dgCoherentBarPrefixHom R D G s 0 (by omega))
        (dgCoherentBarPrefixZeroHom_closed R D G s))) r ≫
      (dgCoherentBarVertexHomologyTransportIso R D G x r
        (dgCoherentBarSource R D G (dgCoherentBarTail s 1 (by omega)))
        (s.obj (⟨1, by omega⟩ : Fin (n + 2))) (dgCoherentBarSource_firstTail_nerve R D G s)).hom =
    (dgCoherentBarSourceHomologyIso R D G x r (n + 1) s).hom ≫
      (dgCoherentBarHomologyDiagram R D G x r).map (s.map (homOfLE
        (show (0 : Fin (n + 2)) ≤ ⟨1, by omega⟩ from Fin.zero_le _))) :=
  dgCoherentBarVertexHomologyTransport_naturality R D G x r
    (dgCoherentBarSource_nerve R D G (n + 1) s) (dgCoherentBarSource_firstTail_nerve R D G s)
    _ _ (dgCoherentBarPrefixCycle_eq_diagramEdge R D G s)

lemma dgCoherentBarSignedPrefixHomologyDiagram {n : ℕ} (s : (nerve J) _⦋n + 1⦌)
    (x : D) (q : ℤ) :
    dgDegreeOneHomologyMap R (dgCoherentBarSignedPrefixCochain R D G s x)
      (dgCoherentBarSignedPrefixCochain_closed R D G s x) q ≫
      (dgComplexShiftHomologyIso R
        ((dgCoherentBarSource R D G (dgCoherentBarTail s 1 (by omega))).obj (Opposite.op x))
        (n : ℤ) (q + 1) (q + ((n : ℤ) + 1)) (by omega)).hom ≫
      (dgCoherentBarVertexHomologyTransportIso R D G x (q + ((n : ℤ) + 1))
        (dgCoherentBarSource R D G (dgCoherentBarTail s 1 (by omega)))
        (s.obj (⟨1, by omega⟩ : Fin (n + 2))) (dgCoherentBarSource_firstTail_nerve R D G s)).hom =
    (dgComplexShiftHomologyIso R
      ((dgCoherentBarSource R D G ⟨n + 1, s⟩).obj (Opposite.op x))
      ((n : ℤ) + 1) q (q + ((n : ℤ) + 1)) (by omega)).hom ≫
      (dgCoherentBarSourceHomologyIso R D G x (q + ((n : ℤ) + 1)) (n + 1) s).hom ≫
        (dgCoherentBarHomologyDiagram R D G x (q + ((n : ℤ) + 1))).map (s.map (homOfLE
          (show (0 : Fin (n + 2)) ≤ ⟨1, by omega⟩ from Fin.zero_le _))) := by
  rw [← Category.assoc, dgCoherentBarSignedPrefixHomology, Category.assoc,
    dgCoherentBarPrefixHomologyDiagram_naturality]

end SerrePositivity.InfinityCategories
