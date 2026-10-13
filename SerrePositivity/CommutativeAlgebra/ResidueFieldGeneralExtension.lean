module

public import SerrePositivity.CommutativeAlgebra.ResidueFieldHistoryGlue
public import SerrePositivity.CommutativeAlgebra.ResidueFieldDirectLimit

/-! # 任意の剰余体拡大を実現する平坦局所拡大

指定体そのものを整列添字にし、実構成した両立履歴から全体図式を貼り合わせる。
その直極限の剰余体を指定体へ同定する。Noether性や完備性は主張しない。
完備Noether版には別途R4の証明が必要。
-/

public section
namespace SerrePositivity
open IsLocalRing
universe u
variable {B K : Type u} [CommRing B] [IsLocalRing B] [Field K]
variable [Algebra (ResidueField B) K] [Algebra B K] [IsScalarTower B (ResidueField B) K]

/-- 整列した生成元の全体上に、実際の平坦局所代数の図式を構成する。 -/
theorem exists_residueField_generatorDiagram [LinearOrder K]
    (wf : WellFounded ((· < ·) : K → K → Prop)) :
    ∃ D : LocalAlgebraDiagram B K K,
      IsResidueFieldDiagram D (residueGeneratorAfter (ResidueField B) K) := by
  obtain ⟨s, hs⟩ := exists_coherent_residueFieldHistories (B := B) wf
  let hq := fun j k (h : j < k) ↦ (hs k).2 j h
  exact ⟨localAlgebraGlueAll s hq,
    residueFieldDiagramGlueAll_spec (residueGeneratorAfter (ResidueField B) K)
      s hq (fun j ↦ (hs j).1)⟩

omit [Algebra B K] [IsScalarTower B (ResidueField B) K] in
/-- 任意の指定剰余体拡大を、同じ宇宙の平坦局所B代数で実現する。
Noether性・完備性・体拡大の有限生成性は仮定しない。 -/
theorem exists_flat_local_extension_of_residueField :
    ∃ (C : Type u) (_ : CommRing C) (_ : IsLocalRing C) (_ : Algebra B C)
      (_ : IsLocalHom (algebraMap B C)),
      Module.Flat B C ∧ (maximalIdeal B).map (algebraMap B C) = maximalIdeal C ∧
      ∃ e : ResidueField C ≃+* K,
        ∀ x, e (ResidueField.map (algebraMap B C) x) = algebraMap (ResidueField B) K x := by
  classical
  let : Algebra B K := ((algebraMap (ResidueField B) K).comp (residue B)).toAlgebra
  let : IsScalarTower B (ResidueField B) K := IsScalarTower.of_algebraMap_eq (fun _ ↦ rfl)
  obtain ⟨ord, hwf⟩ := exists_residueGeneratorOrder K
  let : LinearOrder K := ord
  let : WellFoundedLT K := hwf
  obtain ⟨D, hD⟩ := exists_residueField_generatorDiagram (B := B) (K := K) wellFounded_lt
  let : DirectedSystem D.obj (D.map · · ·) := hD.1
  let : ∀ j, Module.Flat B (D.obj j) := hD.2.2.2.1
  apply exists_flat_local_extension_of_directed_system D.obj D.map hD.2.1
    hD.2.2.2.2.1 D.target hD.2.2.1
  intro x
  have hx : x ∈ Set.range (D.target x) := by
    rw [hD.2.2.2.2.2 x]
    exact residueGeneratorAfter_cover (ResidueField B) K x
  obtain ⟨y, hy⟩ := hx
  exact ⟨x, y, hy⟩

end SerrePositivity
