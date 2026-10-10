module

public import SerrePositivity.HomologicalAlgebra.KProjectiveLift
public import SerrePositivity.HomologicalAlgebra.Resolution
public import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence

/-!
# 各項の大きさを保つ馬蹄構成

## 概要

短完全列の両端の射影分解から、中央の分解を作る。
各項が両端の同じ次数の項の直和になることを明示し、§4 で必要な
共通の次数範囲とランクの制御に使う。

## 証明方針

導来圏の連結射を K 射影性によって鎖写像に持ち上げ、その写像余錐をとる。
分解であることは短完全列の三角形との同型で、項の大きさは写像余錐の項の
直和表示で確かめる。正則局所環の分解存在定理は使用しない。
-/

@[expose] public section

universe u v w

open CategoryTheory Limits Pretriangulated

namespace SerrePositivity

section derived

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

/-- K 射影的な複体からの導来圏の射は鎖写像で表せる。
ホモトピー圏での完全忠実性と、ホモトピー商の射の全射性を組み合わせる。 -/
lemma exists_chainMap_of_derivedHom (P Q : CochainComplex C ℤ) [P.IsKProjective]
    (d : DerivedCategory.Q.obj P ⟶ DerivedCategory.Q.obj Q) :
    ∃ f : P ⟶ Q, DerivedCategory.Q.map f = d := by
  obtain ⟨g, hg⟩ := (CochainComplex.IsKProjective.Qh_map_bijective P
    ((HomotopyCategory.quotient _ _).obj Q)).surjective
      ((DerivedCategory.quotientCompQhIso C).hom.app P ≫ d ≫
        (DerivedCategory.quotientCompQhIso C).inv.app Q)
  obtain ⟨f, rfl⟩ := (HomotopyCategory.quotient _ _).map_surjective g
  refine ⟨f, ?_⟩
  rw [← cancel_epi ((DerivedCategory.quotientCompQhIso C).hom.app P),
    ← (DerivedCategory.quotientCompQhIso C).hom.naturality f]
  change DerivedCategory.Qh.map ((HomotopyCategory.quotient _ _).map f) ≫ _ = _
  rw [hg]
  simp

/-- 導来圏の同型から各次数のホモロジーの同型を得る。
ホモロジー関手の局所化との比較同型を両側に挿入する。 -/
noncomputable def homologyIsoOfDerivedIso (P Q : CochainComplex C ℤ)
    (e : DerivedCategory.Q.obj P ≅ DerivedCategory.Q.obj Q) (i : ℤ) :
    P.homology i ≅ Q.homology i :=
  (DerivedCategory.homologyFunctorFactors C i).symm.app P ≪≫
    (DerivedCategory.homologyFunctor C i).mapIso e ≪≫
      (DerivedCategory.homologyFunctorFactors C i).app Q

end derived

variable {R : Type u} [CommRing R]

/-- 射影分解は導来圏で元の加群の単一複体と同型。
零次ホモロジーへの増大射が擬同型であることを使う。 -/
noncomputable def derivedIsoOfResolution [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    (P : CochainComplex (ModuleCat.{u} R) ℤ) (M : ModuleCat.{u} R)
    (hP : IsResolutionOf P M) :
    DerivedCategory.Q.obj P ≅ (DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj M := by
  let ε := toSingleOfHomology P (d_zero_one_eq_zero P hP.isZero_X) hP.homologyZeroIso.hom
  have : QuasiIso ε := quasiIso_toSingleOfHomology P
    (d_zero_one_eq_zero P hP.isZero_X) hP.homologyZeroIso.hom hP.isZero_homology
  exact asIso (DerivedCategory.Q.map ε)

/-- `Q → P[1]` の写像余錐の `i` 次の項は `Q^i ⊕ P^i`。
二つのシフトの添字を打ち消し、写像錐の直和表示を使う。 -/
noncomputable def extensionCoconeXIso (P Q : CochainComplex (ModuleCat.{u} R) ℤ)
    (f : Q ⟶ P⟦(1 : ℤ)⟧) (i : ℤ) :
    (CochainComplex.mappingCocone f).X i ≅ Q.X i ⊞ P.X i :=
  CochainComplex.shiftFunctorObjXIso (CochainComplex.mappingCone f) (-1) i (i - 1) (by omega) ≪≫
    HomologicalComplex.homotopyCofiber.XIsoBiprod f (i - 1) i (by change i - 1 + 1 = i; omega) ≪≫
      biprod.mapIso (Iso.refl _) (CochainComplex.shiftFunctorObjXIso P 1 (i - 1) i (by omega))

/-- 短完全列の両端の分解を使い、中央の加群を表す写像余錐を構成する。
連結射を持ち上げ、回転した二つの区別三角形の同型から中央の同型を得る。 -/
lemma exists_extensionCocone [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    (S : ShortComplex (ModuleCat.{u} R)) (hS : S.ShortExact)
    (P Q : CochainComplex (ModuleCat.{u} R) ℤ)
    (hP : IsResolutionOf P S.X₁) (hQ : IsResolutionOf Q S.X₃) :
    ∃ f : Q ⟶ P⟦(1 : ℤ)⟧,
      Nonempty (DerivedCategory.Q.obj (CochainComplex.mappingCocone f) ≅
        (DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj S.X₂) := by
  have : ∀ i, Projective (Q.X i) := hQ.projective
  have : Q.IsStrictlyLE 0 := (CochainComplex.isStrictlyLE_iff Q 0).mpr hQ.isZero_X
  have : Q.IsKProjective := CochainComplex.isKProjective_of_projective Q 0
  let eQ := derivedIsoOfResolution Q S.X₃ hQ
  let eP := (DerivedCategory.Q.commShiftIso (1 : ℤ)).app P ≪≫
    (shiftFunctor _ (1 : ℤ)).mapIso (derivedIsoOfResolution P S.X₁ hP)
  obtain ⟨f, hf⟩ := exists_chainMap_of_derivedHom Q (P⟦(1 : ℤ)⟧)
    (eQ.hom ≫ hS.singleδ ≫ eP.inv)
  let T := DerivedCategory.Q.mapTriangle.obj (CochainComplex.mappingCocone.triangle f)
  have hT : T ∈ distTriang _ := DerivedCategory.mappingCocone_triangle_distinguished f
  let e := isoTriangleOfIso₁₂ T.rotate hS.singleTriangle.rotate.rotate
    (rot_of_distTriang _ hT)
    (rot_of_distTriang _ (rot_of_distTriang _ hS.singleTriangle_distinguished))
    eQ eP (by
      change DerivedCategory.Q.map f ≫ eP.hom = eQ.hom ≫ hS.singleδ
      rw [hf]
      simp)
  exact ⟨f, ⟨(shiftFunctor _ (1 : ℤ)).preimageIso (Triangle.π₃.mapIso e)⟩⟩

/-- 短完全列の中央の射影分解で、各項が両端の同じ次数の直和になるものがある。
写像余錐の導来圏での同型からホモロジーを同定し、項の射影性を直和から移す。 -/
theorem exists_horseshoe_resolution
    (S : ShortComplex (ModuleCat.{u} R)) (hS : S.ShortExact)
    (P Q : CochainComplex (ModuleCat.{u} R) ℤ)
    (hP : IsResolutionOf P S.X₁) (hQ : IsResolutionOf Q S.X₃) :
    ∃ E : CochainComplex (ModuleCat.{u} R) ℤ, Nonempty (IsResolutionOf E S.X₂) ∧
      ∀ i, Nonempty (E.X i ≅ Q.X i ⊞ P.X i) := by
  let := HasDerivedCategory.standard (ModuleCat.{u} R)
  obtain ⟨f, ⟨e⟩⟩ := exists_extensionCocone S hS P Q hP hQ
  let E := CochainComplex.mappingCocone f
  let H := fun i ↦ homologyIsoOfDerivedIso E
    ((HomologicalComplex.single _ _ 0).obj S.X₂) e i
  refine ⟨E, ?_, fun i ↦ ⟨extensionCoconeXIso P Q f i⟩⟩
  refine ⟨{
    isZero_X := ?_
    projective := ?_
    isZero_homology := ?_
    homologyZeroIso := H 0 ≪≫ HomologicalComplex.singleObjHomologySelfIso _ 0 S.X₂ }⟩
  · intro i hi
    exact ((biprod_isZero_iff _ _).mpr ⟨hQ.isZero_X i hi, hP.isZero_X i hi⟩).of_iso
      (extensionCoconeXIso P Q f i)
  · intro i
    have := hQ.projective i
    have := hP.projective i
    exact Projective.of_iso (extensionCoconeXIso P Q f i).symm inferInstance
  · intro i hi
    exact (HomologicalComplex.isZero_single_obj_homology _ _ S.X₂ i hi).of_iso (H i)

/-- 馬蹄構成は両端の共通の下限と有限自由性を保ち、各次数の階数は和になる。
§4 の長さに関する帰納法で、段数が増えても分解の次数幅を固定するために使う。 -/
theorem exists_controlled_horseshoe [Nontrivial R]
    (S : ShortComplex (ModuleCat.{u} R)) (hS : S.ShortExact)
    (P Q : CochainComplex (ModuleCat.{u} R) ℤ)
    (hP : IsResolutionOf P S.X₁) (hQ : IsResolutionOf Q S.X₃)
    (hPf : ∀ i, Module.Free R (P.X i)) (hQf : ∀ i, Module.Free R (Q.X i))
    (hPn : ∀ i, Module.Finite R (P.X i)) (hQn : ∀ i, Module.Finite R (Q.X i))
    (a : ℤ) (hPb : ∀ i, i < a → IsZero (P.X i))
    (hQb : ∀ i, i < a → IsZero (Q.X i)) :
    ∃ E : CochainComplex (ModuleCat.{u} R) ℤ, Nonempty (IsResolutionOf E S.X₂) ∧
      (∀ i, Module.Free R (E.X i)) ∧ (∀ i, Module.Finite R (E.X i)) ∧
      (∀ i, i < a → IsZero (E.X i)) ∧
      ∀ i, Module.finrank R (E.X i) = Module.finrank R (P.X i) + Module.finrank R (Q.X i) := by
  obtain ⟨E, hE, he⟩ := exists_horseshoe_resolution S hS P Q hP hQ
  have hf (i : ℤ) : Module.Free R (E.X i) ∧ Module.Finite R (E.X i) := by
    have := hPf i
    have := hQf i
    have := hPn i
    have := hQn i
    obtain ⟨hfree, hfinite⟩ := free_finite_biprod (Q.X i) (P.X i)
    let e := (he i).some.toLinearEquiv
    exact ⟨Module.Free.of_equiv e.symm, Module.Finite.equiv e.symm⟩
  refine ⟨E, hE, fun i ↦ (hf i).1, fun i ↦ (hf i).2, ?_, ?_⟩
  · intro i hi
    exact ((biprod_isZero_iff _ _).mpr ⟨hQb i hi, hPb i hi⟩).of_iso (he i).some
  · intro i
    have := hPf i
    have := hQf i
    have := hPn i
    have := hQn i
    let e := (he i).some ≪≫ ModuleCat.biprodIsoProd (Q.X i) (P.X i)
    rw [e.toLinearEquiv.finrank_eq, Module.finrank_prod, add_comm]

end SerrePositivity
