module

public import SerrePositivity.AlgebraicGeometry.ProjectiveDirectSumHomology

/-!
概要：Čech 版の直和コホモロジー比較に、各成分の包含との対応を付ける。
方針：評価から余極限への自然変換と、Mathlib の NatTrans.app_homology を使う。
規約：原典 Stacks 30.20.1 の Hⁱ の直和を扱うための Čech 版の代数的な入力。
使われ方：Rees 単項式による次数の移動と、コホモロジー比較の両立性。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace SerrePositivity.AlgebraicGeometry

open CategoryTheory CategoryTheory.Limits
open scoped DirectSum

universe u
variable {R : Type u} [CommRing R] {κ : Type} [DecidableEq κ]

/-- 評価から余極限への自然な包含。 -/
def projectiveColimitInclusion (n : κ) :
    (evaluation (Discrete κ) (ModuleCat.{u} R)).obj ⟨n⟩ ⟶ colim where
  app F := colimit.ι F ⟨n⟩
  naturality _F _G f := (colimit.ι_map f ⟨n⟩).symm

variable (S : κ → ShortComplex (ModuleCat.{u} R))

/-- 直和の短複体への各成分の包含。 -/
def projectiveDirectSumShortComplexInclusion (n : κ) :
    S n ⟶ projectiveDirectSumShortComplex S :=
  ShortComplex.homMk
    (ModuleCat.ofHom (DirectSum.lof R κ (fun n ↦ (S n).X₁) n))
    (ModuleCat.ofHom (DirectSum.lof R κ (fun n ↦ (S n).X₂) n))
    (ModuleCat.ofHom (DirectSum.lof R κ (fun n ↦ (S n).X₃) n)) (by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      exact DirectSum.lmap_lof (fun n ↦ (S n).f.hom) n x) (by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      exact DirectSum.lmap_lof (fun n ↦ (S n).g.hom) n x)

/-- 短複体の比較は、余極限への包含を外部直和への包含へ送る。 -/
theorem projectiveShortComplexColimitInclusion_eq (n : κ) :
    (projectiveShortComplexDiagram S).mapNatTrans (projectiveColimitInclusion (R := R) n) ≫
        (projectiveDirectSumShortComplexIso S).hom =
      projectiveDirectSumShortComplexInclusion S n := by
  apply ShortComplex.hom_ext
  · change colimit.ι (Discrete.functor (fun n ↦ (S n).X₁)) ⟨n⟩ ≫
        (projectiveDirectSumColimitIso (fun n ↦ (S n).X₁)).hom = _
    exact projectiveDirectSumColimitIso_ι _ n
  · change colimit.ι (Discrete.functor (fun n ↦ (S n).X₂)) ⟨n⟩ ≫
        (projectiveDirectSumColimitIso (fun n ↦ (S n).X₂)).hom = _
    exact projectiveDirectSumColimitIso_ι _ n
  · change colimit.ι (Discrete.functor (fun n ↦ (S n).X₃)) ⟨n⟩ ≫
        (projectiveDirectSumColimitIso (fun n ↦ (S n).X₃)).hom = _
    exact projectiveDirectSumColimitIso_ι _ n

/-- Čech 版の直和コホモロジー比較は、各成分の包含を保つ。
原典 Stacks 30.20.1 の Hⁱ の直和と Rees 作用の比較に使う。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。 -/
theorem projectiveDirectSumShortComplexHomologyIso_inclusion (n : κ) :
    (ShortComplex.homologyFunctor (ModuleCat.{u} R)).map
        (projectiveDirectSumShortComplexInclusion S n) ≫
      (projectiveDirectSumShortComplexHomologyIso S).hom =
        ModuleCat.ofHom (DirectSum.lof R κ (fun n ↦ (S n).homology) n) := by
  let P := projectiveShortComplexDiagram S
  let F := (evaluation (Discrete κ) (ModuleCat.{u} R)).obj ⟨n⟩
  let L := colim (J := Discrete κ) (C := ModuleCat.{u} R)
  let H := ShortComplex.homologyFunctor (ModuleCat.{u} R)
  let a := P.mapHomologyIso F
  let b := P.mapHomologyIso L
  let t := projectiveDirectSumShortComplexIso S
  let d := projectiveShortComplexDiagramHomologyIso S
  let c := projectiveDirectSumColimitIso (fun n ↦ (S n).homology)
  let v := P.mapNatTrans (projectiveColimitInclusion (R := R) n)
  have hinc : v ≫ t.hom = projectiveDirectSumShortComplexInclusion S n :=
    projectiveShortComplexColimitInclusion_eq S n
  have hv : H.map v ≫ b.hom = a.hom ≫ colimit.ι P.homology ⟨n⟩ := by
    have hn := NatTrans.app_homology (projectiveColimitInclusion (R := R) n) P
    change colimit.ι P.homology ⟨n⟩ = a.inv ≫ H.map v ≫ b.hom at hn
    rw [hn]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
  calc
    _ = H.map v ≫ b.hom ≫ L.map d.hom ≫ c.hom := by
      rw [← hinc, H.map_comp]
      change (H.map v ≫ (H.mapIso t).hom) ≫
        ((H.mapIso t).inv ≫ b.hom ≫ L.map d.hom ≫ c.hom) = _
      simp only [Category.assoc, Iso.hom_inv_id_assoc]
    _ = a.hom ≫ colimit.ι P.homology ⟨n⟩ ≫ L.map d.hom ≫ c.hom := by
      rw [← Category.assoc, hv]
      simp only [Category.assoc]
    _ = _ := by
      rw [colimit.ι_map_assoc]
      change a.hom ≫ a.inv ≫
        colimit.ι (Discrete.functor (fun n ↦ (S n).homology)) ⟨n⟩ ≫ c.hom = _
      rw [Iso.hom_inv_id_assoc]
      exact projectiveDirectSumColimitIso_ι _ n

/-- Čech 版の直和コホモロジー比較は、成分を別の次数へ送る写像にも自然。
原典 Stacks 30.20.1 の Hⁱ と Rees 単項式の作用の比較に使う。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。 -/
theorem projectiveDirectSumShortComplexHomologyIso_naturality_component
    {κ' : Type} [DecidableEq κ'] (T : κ' → ShortComplex (ModuleCat.{u} R))
    (f : projectiveDirectSumShortComplex S ⟶ projectiveDirectSumShortComplex T)
    (n : κ) (m : κ') (g : S n ⟶ T m)
    (h : projectiveDirectSumShortComplexInclusion S n ≫ f =
      g ≫ projectiveDirectSumShortComplexInclusion T m) :
    ModuleCat.ofHom (DirectSum.lof R κ (fun n ↦ (S n).homology) n) ≫
        (projectiveDirectSumShortComplexHomologyIso S).inv ≫
        (ShortComplex.homologyFunctor (ModuleCat.{u} R)).map f ≫
        (projectiveDirectSumShortComplexHomologyIso T).hom =
      (ShortComplex.homologyFunctor (ModuleCat.{u} R)).map g ≫
        ModuleCat.ofHom (DirectSum.lof R κ' (fun m ↦ (T m).homology) m) := by
  let H := ShortComplex.homologyFunctor (ModuleCat.{u} R)
  rw [← projectiveDirectSumShortComplexHomologyIso_inclusion S n]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [← H.map_comp_assoc, h, H.map_comp_assoc,
    projectiveDirectSumShortComplexHomologyIso_inclusion T m]

end SerrePositivity.AlgebraicGeometry
