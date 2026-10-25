module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.AppendSimplex
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.Diagram
public import SerrePositivity.InfinityCategories.Derived.DGCoherentBarFaceDifferential

/-!
概要：上界付加による局所縮約の次数 −1 の実 bar 係数を作る。
方針：始点を保持する shift 単位ブロックを、上界付加した単体の因子へ輸送する。
規約：元の全 dg 加群 Hom と正規化射影を使う。
使われ方：有限 support の共通上界における bar 縮約。
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
  {J : Type u} [PartialOrder J] (F : J ⥤ ModuleCategory R D) {n : ℕ}

lemma dgStrictAppendSource (s : (nerve J) _⦋n⦌) (b : J)
    (hb : s.obj (Fin.last n) ≤ b) :
    dgCoherentBarSource R D (dgCoherentBarStrictDiagram R D F)
        ⟨n + 1, dgStrictAppendSimplex s b hb⟩ =
      dgCoherentBarSource R D (dgCoherentBarStrictDiagram R D F) ⟨n, s⟩ := by
  rw [dgCoherentBarStrictSource, dgCoherentBarStrictSource]
  change ForgetEnrichment.to (Complex R)
      (F.obj ((dgStrictAppendSimplex s b hb).obj (0 : Fin (n + 1)).castSucc)) = _
  rw [dgStrictAppendSimplex_obj_castSucc]

def dgStrictAppendBlock (s : (nerve J) _⦋n⦌) (b : J)
    (hb : s.obj (Fin.last n) ≤ b) :
    (moduleHom R D
      (ForgetEnrichment.to (Complex R)
        (dgCoherentBarFamily R D (dgCoherentBarStrictDiagram R D F) ⟨n, s⟩))
      (ForgetEnrichment.to (Complex R)
        (dgCoherentBarFamily R D (dgCoherentBarStrictDiagram R D F)
          ⟨n + 1, dgStrictAppendSimplex s b hb⟩))).X (-1) :=
  (dgModuleHomTargetTransport R D
    (shiftModule (n : ℤ) (dgCoherentBarSource R D (dgCoherentBarStrictDiagram R D F) ⟨n, s⟩))
    (shiftModule ((n + 1 : ℕ) : ℤ)
      (dgCoherentBarSource R D (dgCoherentBarStrictDiagram R D F) ⟨n, s⟩))
    (shiftModule ((n + 1 : ℕ) : ℤ)
      (dgCoherentBarSource R D (dgCoherentBarStrictDiagram R D F)
        ⟨n + 1, dgStrictAppendSimplex s b hb⟩))
    (congrArg (shiftModule ((n + 1 : ℕ) : ℤ)) (dgStrictAppendSource R D F s b hb)).symm (-1)
    (moduleHomShiftBlock R D (n : ℤ) ((n + 1 : ℕ) : ℤ)
      (unitElement R (dgCoherentBarSource R D (dgCoherentBarStrictDiagram R D F) ⟨n, s⟩)).val
      (by omega))).val

lemma dgStrictAppendBlock_heq (s : (nerve J) _⦋n⦌) (b : J)
    (hb : s.obj (Fin.last n) ≤ b) :
    HEq (dgStrictAppendBlock R D F s b hb)
      (moduleHomShiftBlock R D (n : ℤ) ((n + 1 : ℕ) : ℤ)
        (unitElement R (dgCoherentBarSource R D (dgCoherentBarStrictDiagram R D F) ⟨n, s⟩)).val
        (show (n : ℤ) + 0 - ((n + 1 : ℕ) : ℤ) = -1 by omega)) := by
  exact (dgModuleHomTargetTransport R D _ _ _
    (congrArg (shiftModule ((n + 1 : ℕ) : ℤ)) (dgStrictAppendSource R D F s b hb)).symm (-1)
    (moduleHomShiftBlock R D (n : ℤ) ((n + 1 : ℕ) : ℤ)
      (unitElement R (dgCoherentBarSource R D (dgCoherentBarStrictDiagram R D F) ⟨n, s⟩)).val
      (by omega))).property

def dgStrictAppendColumn (s : (nerve J) _⦋n⦌) (b : J)
    (hb : s.obj (Fin.last n) ≤ b) :
    (moduleHom R D
      (ForgetEnrichment.to (Complex R)
        (dgCoherentBarFamily R D (dgCoherentBarStrictDiagram R D F) ⟨n, s⟩))
      (ForgetEnrichment.to (Complex R)
        (dgCoherentBarNormalizedGraded R D (dgCoherentBarStrictDiagram R D F)))).X (-1) :=
  (eHomWhiskerLeft (Complex R)
    (dgCoherentBarFamily R D (dgCoherentBarStrictDiagram R D F) ⟨n, s⟩)
    (Sigma.ι (dgCoherentBarFamily R D (dgCoherentBarStrictDiagram R D F))
      ⟨n + 1, dgStrictAppendSimplex s b hb⟩ ≫
        dgCoherentBarNormalizedProjection R D (dgCoherentBarStrictDiagram R D F))).f (-1)
    (dgStrictAppendBlock R D F s b hb)

end SerrePositivity.InfinityCategories
