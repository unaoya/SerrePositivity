module
public import SerrePositivity.DifferentialGraded.Verdier.Tria

/-! # Verdier 商で殺される対象と retract 閉包

既存の分数計算と三角形の Hom 完全性を使い、零対象の逆像を判定する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits Pretriangulated
open scoped ZeroObject

section
variable {C : Type*} [Category* C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] [IsTriangulated C]
  (P : ObjectProperty C) [P.IsTriangulated]

/-- 三角部分圏による Verdier 商は、ちょうどその retract 閉包を殺す。 -/
lemma verdierQuotient_isZero_iff_retractClosure (X : C) :
    IsZero (P.trW.Q.obj X) ↔ P.retractClosure X := by
  constructor
  · intro hX
    have hmap : P.trW.Q.map (𝟙 X) = P.trW.Q.map (0 : X ⟶ X) := by
      rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_zero]
      exact (IsZero.iff_id_eq_zero _).1 hX
    obtain ⟨Y, s, hs, hfac⟩ :=
      (MorphismProperty.map_eq_iff_precomp P.trW.Q P.trW (𝟙 X) 0).1 hmap
    have hs0 : s = 0 := by simpa only [Category.comp_id, Limits.comp_zero] using hfac
    obtain ⟨Z, g, h, hT, hZ⟩ := hs
    obtain ⟨r, hr⟩ := Triangle.yoneda_exact₂ _ hT (𝟙 X)
      (by change s ≫ 𝟙 X = 0; rw [Category.comp_id]; exact hs0)
    exact ⟨Z, hZ, ⟨{ i := g, r := r, retract := hr.symm }⟩⟩
  · rintro ⟨Y, hY, ⟨r⟩⟩
    exact (triangulatedKernel P.trW.Q).prop_of_retract r (verdierQuotient_isZero P Y hY)

/-- 商の三角関手の核を、元の対象クラスで記述する。 -/
lemma verdierQuotient_kernel_eq_retractClosure :
    triangulatedKernel P.trW.Q = P.retractClosure := by
  funext X
  exact propext (verdierQuotient_isZero_iff_retractClosure P X)

/-- 三角部分圏の thick 閉包は retract 閉包だけで得られる。 -/
lemma triangEnvelope_eq_retractClosure : P.triangEnvelope = P.retractClosure := by
  have : P.retractClosure.IsTriangulated := by
    rw [← verdierQuotient_kernel_eq_retractClosure P]
    infer_instance
  apply le_antisymm
  · exact P.triangEnvelope_le_iff.2 P.le_retractClosure
  · exact (ObjectProperty.retractClosure_le_iff P P.triangEnvelope).2 P.le_triangEnvelope

end

universe u v
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- tria 内の retract 閉包と、同じ導来対象に対する Perf_S は一致する。 -/
lemma triaImage_retractClosure_iff_perfect (S : Set D) (X : TriaCategory A D) :
    (triaImage A D S).retractClosure X ↔ modulePerfectOver A D S X.obj := by
  constructor
  · rintro ⟨Y, hY, ⟨r⟩⟩
    exact ObjectProperty.prop_retractClosure hY (r.map (triaInclusion A D))
  · rintro ⟨Y, hY, ⟨r⟩⟩
    have hYu : derivedFiniteCellOver A D Set.univ Y :=
      ObjectProperty.map_monotone
        (fun _ hM => moduleFiniteCellOver_mono A D (Set.subset_univ S) hM)
        (moduleToDerived A D) Y hY
    let Y' : TriaCategory A D := ⟨Y, hYu⟩
    let r' : Retract X Y' :=
      { i := ObjectProperty.homMk r.i
        r := ObjectProperty.homMk r.r
        retract := by ext; exact r.retract }
    exact ⟨Y', hY, ⟨r'⟩⟩

/-- U17a の零対象判定。tria(S) の retract 閉包との一致を明示する。 -/
lemma triaQuotient_isZero_iff (S : Set D) (X : TriaCategory A D) :
    IsZero ((triaQuotient A D S).obj X) ↔ (triaImage A D S).retractClosure X :=
  verdierQuotient_isZero_iff_retractClosure (triaImage A D S) X

lemma triaQuotient_isZero_iff_triaNull (S : Set D) (X : TriaCategory A D) :
    IsZero ((triaQuotient A D S).obj X) ↔ triaNull A D S X := by
  rw [triaNull, triangEnvelope_eq_retractClosure]
  exact triaQuotient_isZero_iff A D S X

lemma triaQuotient_isZero_iff_perfect (S : Set D) (X : TriaCategory A D) :
    IsZero ((triaQuotient A D S).obj X) ↔ modulePerfectOver A D S X.obj :=
  (triaQuotient_isZero_iff A D S X).trans
    (triaImage_retractClosure_iff_perfect A D S X)

end SerrePositivity.DifferentialGraded
