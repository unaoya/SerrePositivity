module
public import SerrePositivity.DifferentialGraded.Endomorphism.ShortExactComparison
public import SerrePositivity.DifferentialGraded.Endomorphism.HomComparisonShift
public import SerrePositivity.DifferentialGraded.Module.GradedSplitHomExact
public import SerrePositivity.DifferentialGraded.Module.ConeGradedSplit

/-! # 全次数分裂のHom短完全列による再構成Hom比較のcone閉性 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded
open CategoryTheory HomologicalComplex Pretriangulated
variable (A : Type u) [CommRing A] (D : Type v) (B : Type w)
  [DGCategory A D] [DGCategory A B] [Small.{u} D] [Small.{u} B]
variable (F : DGFunctor A (RightModule A D) (RightModule A B))

/-- 全Hom写像を、全次数分裂のHom短完全列の間の射として保持する。 -/
def dgHomMapShortComplex {M N P : ModuleCategory A D} {f : M ⟶ N} {g : N ⟶ P}
    (s : ModuleGradedSplit A D f g) (T : ModuleCategory A D) :
    s.homShortComplex T ⟶
      (dgModuleFunctorGradedSplit A D B F s).homShortComplex (F.onClosed.obj T) where
  τ₁ := F.map P T
  τ₂ := F.map N T
  τ₃ := F.map M T
  comm₁₂ := (dgHomMap_precompose F g T).symm
  comm₂₃ := (dgHomMap_precompose F f T).symm

lemma dgHomMap_gradedSplit_middle {M N P : ModuleCategory A D} {f : M ⟶ N} {g : N ⟶ P}
    (s : ModuleGradedSplit A D f g) (T : ModuleCategory A D)
    (hP : QuasiIso (F.map P T)) (hM : QuasiIso (F.map M T)) : QuasiIso (F.map N T) :=
  complexQuasiIso_middle_of_shortExact (dgHomMapShortComplex A D B F s T)
    (s.homShortComplex_shortExact T)
    ((dgModuleFunctorGradedSplit A D B F s).homShortComplex_shortExact (F.onClosed.obj T)) hP hM

variable (E : RightModule A D)

lemma endomorphismHomComparison_cone {M N : ModuleCategory A D} (f : M ⟶ N)
    (T : ModuleCategory A D)
    (hM : QuasiIso ((endomorphismModuleHom A D E).map M T))
    (hN : QuasiIso ((endomorphismModuleHom A D E).map N T)) :
    QuasiIso ((endomorphismModuleHom A D E).map (moduleCone A D f) T) :=
  dgHomMap_gradedSplit_middle A D (EndomorphismObject E) (endomorphismModuleHom A D E)
    (moduleConeGradedSplit A D f) T
    (endomorphismHomComparison_shift A D E 1 M T hM) hN

lemma endomorphismHomComparisonLocus_triangle_obj₃
    (T : Triangle (ModuleHomotopyCategory A D))
    (hT : T ∈ distTriang (ModuleHomotopyCategory A D))
    (h₁ : endomorphismHomComparisonLocus A D E T.obj₁)
    (h₂ : endomorphismHomComparisonLocus A D E T.obj₂) :
    endomorphismHomComparisonLocus A D E T.obj₃ := by
  obtain ⟨M, N, f, ⟨e⟩⟩ := hT
  have hM := (endomorphismHomComparisonLocus A D E).prop_of_iso (Triangle.π₁.mapIso e) h₁
  have hN := (endomorphismHomComparisonLocus A D E).prop_of_iso (Triangle.π₂.mapIso e) h₂
  apply (endomorphismHomComparisonLocus A D E).prop_of_iso (Triangle.π₃.mapIso e.symm)
  intro Q
  exact endomorphismHomComparison_cone A D E f Q (hM Q) (hN Q)

instance endomorphismHomComparisonLocusTriangulatedClosed₃ :
    (endomorphismHomComparisonLocus A D E).IsTriangulatedClosed₃ :=
  ObjectProperty.IsTriangulatedClosed₃.mk'
    (endomorphismHomComparisonLocus_triangle_obj₃ A D E)

instance endomorphismHomComparisonLocusTriangulatedClosed₂ :
    (endomorphismHomComparisonLocus A D E).IsTriangulatedClosed₂ :=
  ObjectProperty.IsTriangulatedClosed₂.of_isTriangulatedClosed₃

instance endomorphismHomComparisonLocusNonempty :
    (endomorphismHomComparisonLocus A D E).Nonempty :=
  ObjectProperty.nonempty_of_prop (endomorphismHomComparisonLocus_generator A D E)

instance endomorphismHomComparisonLocusContainsZero :
    (endomorphismHomComparisonLocus A D E).ContainsZero := inferInstance

instance endomorphismHomComparisonLocusIsTriangulated :
    (endomorphismHomComparisonLocus A D E).IsTriangulated where

end SerrePositivity.DifferentialGraded
