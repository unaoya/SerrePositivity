module

public import SerrePositivity.PerfectComplex.HomotopyCategory
public import SerrePositivity.PerfectComplex.K0
public import SerrePositivity.CategoryTheory.TriangulatedK0
public import Mathlib.RingTheory.LocalRing.Module

/-! # 有限自由モデルと有限射影ホモトピー圏の Grothendieck 群

任意の環では比較写像を構成する。局所環では有限射影加群の自由性を使って逆写像を作る。
-/

@[expose] public section

universe u

namespace SerrePositivity

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

variable {R : Type u} [CommRing R] {e : ℕ} {z : Fin e → R}

/-- 既存の有限自由モデルは、新しい有限射影モデルの条件を満たす。 -/
lemma IsPerfectSupported.strictlyPerfect {P : CochainComplex (ModuleCat.{u} R) ℤ}
    (hP : IsPerfectSupported z P) : strictlyPerfectComplex R P := by
  refine ⟨?_, fun q ↦ ?_⟩
  · obtain ⟨a, b, hab⟩ := hP.bounded
    exact ⟨a, b, (P.isStrictlyGE_iff a).mpr (fun q hq ↦ hab q (Or.inl hq)),
      (P.isStrictlyLE_iff b).mpr (fun q hq ↦ hab q (Or.inr hq))⟩
  · have := hP.free q
    exact ⟨hP.finite q, Module.Projective.of_free⟩

/-- 有限自由モデルの対象を有限射影ホモトピー圏へ送る。 -/
def perfSuppHomotopyObj (P : PerfSupp R z) : SupportedPerfectHomotopy z :=
  ⟨perfectHomotopyObj R P.1 P.2.strictlyPerfect,
    (perfectHomotopyObj_supported_iff z P.1 P.2.strictlyPerfect).mpr P.2.supported⟩

/-- ホモトピー同値は支持つき有限射影ホモトピー圏の同型を与える。 -/
noncomputable def perfSuppHomotopyIso (P Q : PerfSupp R z) (h : HomotopyEquiv P.1 Q.1) :
    perfSuppHomotopyObj P ≅ perfSuppHomotopyObj Q :=
  ObjectProperty.isoMk _ (ObjectProperty.isoMk _ (HomotopyCategory.isoOfHomotopyEquiv h))

/-- 具体的な写像錐の三角形を支持つき有限射影圏に入れる。 -/
noncomputable def perfSuppConeTriangle (P Q : PerfSupp R z) (f : P.1 ⟶ Q.1) :
    Triangle (SupportedPerfectHomotopy z) :=
  Triangle.mk
    (ObjectProperty.homMk (ObjectProperty.homMk ((homotopyQuot R).map f)))
    (ObjectProperty.homMk (ObjectProperty.homMk
      ((CochainComplex.mappingCone.triangleh f).mor₂)))
    (ObjectProperty.homMk (ObjectProperty.homMk
      ((CochainComplex.mappingCone.triangleh f).mor₃ ≫
        ((supportedPerfectInclusion z ⋙ perfectHomotopyInclusion R).commShiftIso
          (1 : ℤ)).inv.app (perfSuppHomotopyObj P))))
    (X := perfSuppHomotopyObj P) (Y := perfSuppHomotopyObj Q)
    (Z := perfSuppHomotopyObj ⟨CochainComplex.mappingCone f, P.2.mappingCone f Q.2⟩)

set_option backward.isDefEq.respectTransparency false in
lemma perfSuppConeTriangle_distinguished (P Q : PerfSupp R z) (f : P.1 ⟶ Q.1) :
    perfSuppConeTriangle P Q f ∈ distTriang _ := by
  change (perfectHomotopyInclusion R).mapTriangle.obj
    ((supportedPerfectInclusion z).mapTriangle.obj (perfSuppConeTriangle P Q f)) ∈ distTriang _
  convert HomotopyCategory.mappingCone_triangleh_distinguished f using 1
  · simp [perfSuppConeTriangle, Functor.mapTriangle, Functor.commShiftIso_comp_inv_app,
      Category.assoc, perfSuppHomotopyObj, perfectHomotopyObj, homotopyQuot,
      CochainComplex.mappingCone.triangle]

/-- 任意の可換環で定義される、有限自由モデルから有限射影版への比較写像。 -/
noncomputable def freeToPerfectK0 : K0Supported R z →+
    TriangulatedK0 (SupportedPerfectHomotopy z) :=
  K0.lift (fun P ↦ TriangulatedK0.mk (perfSuppHomotopyObj P))
    (fun P Q h ↦ TriangulatedK0.mk_iso (perfSuppHomotopyIso P Q h)) (by
      intro P Q f hc
      have h := TriangulatedK0.mk_triangle _ (perfSuppConeTriangle_distinguished P Q f)
      change TriangulatedK0.mk (perfSuppHomotopyObj Q) =
        TriangulatedK0.mk (perfSuppHomotopyObj P) +
          TriangulatedK0.mk (perfSuppHomotopyObj ⟨CochainComplex.mappingCone f, hc⟩) at h
      exact eq_sub_of_add_eq' h.symm)

@[simp] lemma freeToPerfectK0_mk (P : PerfSupp R z) :
    freeToPerfectK0 (K0.mk P) = TriangulatedK0.mk (perfSuppHomotopyObj P) := K0.lift_mk ..

section Local

variable [IsLocalRing R]

/-- 局所環上では、有限射影代表を既存の有限自由モデルの対象として扱える。 -/
def perfectFreeRepresentative (X : SupportedPerfectHomotopy z) : PerfSupp R z := by
  let P : CochainComplex (ModuleCat.{u} R) ℤ := X.obj.obj.as
  have hp : strictlyPerfectComplex R P :=
    (perfectHomotopyProperty_quotient R P).mp X.obj.property
  refine ⟨P, ⟨?_, ?_, fun q ↦ (hp.2 q).1, ?_⟩⟩
  · obtain ⟨a, b, ha, hb⟩ := hp.1
    exact ⟨a, b, fun q hq ↦ hq.elim (fun h ↦ P.isZero_of_isStrictlyGE a q h)
      (fun h ↦ P.isZero_of_isStrictlyLE b q h)⟩
  · intro q
    have := (hp.2 q).1
    have := (hp.2 q).2
    exact Module.free_of_flat_of_isLocalRing
  · exact (perfectHomotopyObj_supported_iff z P hp).mp X.property

/-- 局所環上の代表複体の類はホモトピー圏の同型で不変。 -/
lemma perfectFreeRepresentative_iso {X Y : SupportedPerfectHomotopy z} (i : X ≅ Y) :
    K0.mk (perfectFreeRepresentative X) = K0.mk (perfectFreeRepresentative Y) :=
  K0.mk_eq_of_homotopyEquiv _ _ (HomotopyCategory.homotopyEquivOfIso
    ((supportedPerfectInclusion z ⋙ perfectHomotopyInclusion R).mapIso i))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- 局所環上の代表複体の類は完全三角形で加法的。 -/
lemma perfectFreeRepresentative_triangle (T : Triangle (SupportedPerfectHomotopy z))
    (hT : T ∈ distTriang _) :
    K0.mk (perfectFreeRepresentative T.obj₂) =
      K0.mk (perfectFreeRepresentative T.obj₁) + K0.mk (perfectFreeRepresentative T.obj₃) := by
  let I := supportedPerfectInclusion z ⋙ perfectHomotopyInclusion R
  let P := perfectFreeRepresentative T.obj₁
  let Q := perfectFreeRepresentative T.obj₂
  obtain ⟨f : P.1 ⟶ Q.1, hf⟩ := (homotopyQuot R).map_surjective (I.map T.mor₁)
  let e := Triangle.π₃.mapIso (isoTriangleOfIso₁₂ (I.mapTriangle.obj T)
    (CochainComplex.mappingCone.triangleh f) (I.map_distinguished T hT)
    (HomotopyCategory.mappingCone_triangleh_distinguished f) (Iso.refl _) (Iso.refl _)
    (by simpa using hf.symm))
  have he := K0.mk_eq_of_homotopyEquiv (perfectFreeRepresentative T.obj₃)
    ⟨CochainComplex.mappingCone f, P.2.mappingCone f Q.2⟩
    (HomotopyCategory.homotopyEquivOfIso e)
  rw [he, K0.mk_cone]
  change K0.mk Q = K0.mk P + (K0.mk Q - K0.mk P)
  abel

/-- 局所環上の比較写像の逆。 -/
noncomputable def perfectToFreeK0 :
    TriangulatedK0 (SupportedPerfectHomotopy z) →+ K0Supported R z :=
  TriangulatedK0.lift (fun X ↦ K0.mk (perfectFreeRepresentative X))
    (fun i ↦ perfectFreeRepresentative_iso i) perfectFreeRepresentative_triangle

@[simp] lemma perfectToFreeK0_mk (X : SupportedPerfectHomotopy z) :
    perfectToFreeK0 (TriangulatedK0.mk X) = K0.mk (perfectFreeRepresentative X) :=
  TriangulatedK0.lift_mk ..

lemma perfectToFreeK0_comp_freeToPerfectK0 :
    (perfectToFreeK0 (z := z)).comp freeToPerfectK0 = AddMonoidHom.id _ := by
  apply K0.hom_ext
  intro P
  simp only [AddMonoidHom.comp_apply, freeToPerfectK0_mk, perfectToFreeK0_mk,
    AddMonoidHom.id_apply]
  rfl

lemma freeToPerfectK0_comp_perfectToFreeK0 :
    (freeToPerfectK0 (z := z)).comp perfectToFreeK0 = AddMonoidHom.id _ := by
  apply TriangulatedK0.hom_ext
  intro X
  simp only [AddMonoidHom.comp_apply, freeToPerfectK0_mk, perfectToFreeK0_mk,
    AddMonoidHom.id_apply]
  exact TriangulatedK0.mk_iso (ObjectProperty.isoMk _ (ObjectProperty.isoMk _ (Iso.refl _)))

/-- 局所環上での旧有限自由モデルと有限射影版の Grothendieck 群の同型。 -/
noncomputable def freePerfectK0Equiv : K0Supported R z ≃+
    TriangulatedK0 (SupportedPerfectHomotopy z) where
  toFun := freeToPerfectK0
  invFun := perfectToFreeK0
  left_inv x := DFunLike.congr_fun perfectToFreeK0_comp_freeToPerfectK0 x
  right_inv x := DFunLike.congr_fun freeToPerfectK0_comp_perfectToFreeK0 x
  map_add' := freeToPerfectK0.map_add

end Local

end SerrePositivity
