module

public import SerrePositivity.AlgebraicGeometry.CechIntegerLiftTotalFunctor
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

/-!
概要：複体値の二重複体の三重totalを、二つの括り方で同じ直和へ比較する。
方針：次数での評価の余積保存と、既存のtotalのdesc・標準入射を使う。
規約：紙の略記は型で完全に展開し、新しい係数や全複体を定義しない。
使われ方：二重Čechの係数複体の三重totalの比較（計画 C01・C02）。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory CategoryTheory.Limits
universe u
set_option backward.isDefEq.respectTransparency false
local notation "up" => ComplexShape.up ℕ

/-- 元の三つの次数の直和を、同じtotalの二つの括り方で比較する成分同型。 -/
def cechTripleTotalComponentIso
    (K : HomologicalComplex₂ (CochainComplex (ModuleCat.{u} ℤ) ℕ) up up) (n : ℕ) : (HomologicalComplex₂.total (C := ModuleCat.{u} ℤ)
      (HomologicalComplex₂.total (C := CochainComplex (ModuleCat.{u} ℤ) ℕ) K up) up).X n ≅
    (HomologicalComplex₂.total (C := ModuleCat.{u} ℤ)
      ((cechIntegerLiftTotalFunctor.mapHomologicalComplex up).obj K) up).X n := by
  let KT : HomologicalComplex₂ (ModuleCat.{u} ℤ) up up :=
    HomologicalComplex₂.total (C := CochainComplex (ModuleCat.{u} ℤ) ℕ) K up
  let KM : HomologicalComplex₂ (ModuleCat.{u} ℤ) up up :=
    (cechIntegerLiftTotalFunctor.mapHomologicalComplex up).obj K
  let V (d : ℕ) := K.toGradedObject.mapObjFun (ComplexShape.π up up up) d
  let ev (c : ℕ) := HomologicalComplex.eval (ModuleCat.{u} ℤ) up c
  let E (d c : ℕ) := PreservesCoproduct.iso (ev c) (V d)
  let l (a b c : ℕ) (h : a+b+c=n) :=
    (HomologicalComplex₂.ιTotal K up a b (a+b) (by rfl)).f c ≫ KT.ιTotal up (a+b) c n h
  let r (a b c : ℕ) (h : a+b+c=n) :=
    HomologicalComplex₂.ιTotal (C := ModuleCat.{u} ℤ) (K.X a) up b c (b+c) (by rfl) ≫
      KM.ιTotal up a (b+c) n (by change a+(b+c)=n; omega)
  let forward : (HomologicalComplex₂.total KT up).X n ⟶ (HomologicalComplex₂.total KM up).X n :=
    KT.totalDesc (c₁₂ := up) (fun d c hdc ↦ (E d c).hom ≫ Sigma.desc (fun j ↦
      r j.1.1 j.1.2 c (by
        have hj : j.1.1+j.1.2=d := j.2
        have hn : d+c=n := hdc
        omega)))
  let backward : (HomologicalComplex₂.total KM up).X n ⟶ (HomologicalComplex₂.total KT up).X n :=
    KM.totalDesc (c₁₂ := up) (fun a d had ↦
      HomologicalComplex₂.totalDesc (K.X a) (c₁₂ := up) (fun b c hbc ↦
        l a b c (by
          have h1 : b+c=d := hbc
          have h2 : a+d=n := had
          omega)))
  have hf (a b c : ℕ) (h : a+b+c=n) : l a b c h ≫ forward = r a b c h := by
    have hi : (HomologicalComplex₂.ιTotal K up a b (a+b) (by rfl)).f c ≫
        (E (a+b) c).hom = Sigma.ι (fun j ↦ ((V (a+b)) j).X c) ⟨(a,b), rfl⟩ := by
      apply (Iso.eq_comp_inv (E (a+b) c)).mp
      change (ev c).map (Sigma.ι (V (a+b)) ⟨(a,b), rfl⟩) =
        Sigma.ι (fun j ↦ (ev c).obj ((V (a+b)) j)) ⟨(a,b), rfl⟩ ≫
          (PreservesCoproduct.iso (ev c) (V (a+b))).inv
      rw [PreservesCoproduct.inv_hom]
      exact (ι_comp_sigmaComparison (ev c) (V (a+b)) ⟨(a,b), rfl⟩).symm
    dsimp only [l, forward]
    rw [Category.assoc, HomologicalComplex₂.ι_totalDesc, ← Category.assoc, hi, Sigma.ι_desc]
  have hg (a b c : ℕ) (h : a+b+c=n) : r a b c h ≫ backward = l a b c h := by
    dsimp only [r, backward]
    simp only [Category.assoc, HomologicalComplex₂.ι_totalDesc]
  refine { hom := forward, inv := backward, hom_inv_id := ?_, inv_hom_id := ?_ }
  · apply HomologicalComplex₂.total.hom_ext (K := KT)
    intro d c hdc
    apply (isColimitOfHasCoproductOfPreservesColimit (ev c) (V d)).hom_ext
    rintro ⟨⟨⟨a,b⟩, hab⟩⟩
    have hab' : a+b=d := hab
    subst d
    have h : a+b+c=n := hdc
    simp only [← Category.assoc]
    change (l a b c h ≫ forward) ≫ backward = l a b c h ≫ 𝟙 _
    rw [hf a b c h, hg a b c h, Category.comp_id]
  · apply HomologicalComplex₂.total.hom_ext (K := KM)
    intro a d had
    apply HomologicalComplex₂.total.hom_ext (K := K.X a)
    intro b c hbc
    have hbc' : b+c=d := hbc
    subst d
    have h : a+b+c=n := by
      have h' : a+(b+c)=n := had
      omega
    simp only [← Category.assoc]
    change (r a b c h ≫ backward) ≫ forward = r a b c h ≫ 𝟙 _
    rw [hg a b c h, hf a b c h, Category.comp_id]

/-- 同じ成分同型は、三つの元の次数の標準入射を保つ。 -/
theorem cechTripleTotalComponentIso_ι
    (K : HomologicalComplex₂ (CochainComplex (ModuleCat.{u} ℤ) ℕ) up up)
    (a b c n : ℕ) (hn : a+b+c=n) :
    ((HomologicalComplex₂.ιTotal K up a b (a+b) (by rfl)).f c ≫
      HomologicalComplex₂.ιTotal (C := ModuleCat.{u} ℤ)
        (HomologicalComplex₂.total (C := CochainComplex (ModuleCat.{u} ℤ) ℕ) K up)
        up (a+b) c n hn) ≫ (cechTripleTotalComponentIso K n).hom =
      HomologicalComplex₂.ιTotal (C := ModuleCat.{u} ℤ) (K.X a) up b c (b+c) (by rfl) ≫
        HomologicalComplex₂.ιTotal (C := ModuleCat.{u} ℤ)
          ((cechIntegerLiftTotalFunctor.mapHomologicalComplex up).obj K) up a (b+c) n
          (by change a+(b+c)=n; omega) := by
  let V := K.toGradedObject.mapObjFun (ComplexShape.π up up up) (a+b)
  let ev := HomologicalComplex.eval (ModuleCat.{u} ℤ) up c
  have hi : (HomologicalComplex₂.ιTotal K up a b (a+b) (by rfl)).f c ≫
      (PreservesCoproduct.iso ev V).hom = Sigma.ι (fun j ↦ (V j).X c) ⟨(a,b), rfl⟩ := by
    apply (Iso.eq_comp_inv (PreservesCoproduct.iso ev V)).mp
    change ev.map (Sigma.ι V ⟨(a,b), rfl⟩) =
      Sigma.ι (fun j ↦ ev.obj (V j)) ⟨(a,b), rfl⟩ ≫ (PreservesCoproduct.iso ev V).inv
    rw [PreservesCoproduct.inv_hom]
    exact (ι_comp_sigmaComparison ev V ⟨(a,b), rfl⟩).symm
  dsimp only [cechTripleTotalComponentIso]
  rw [Category.assoc, HomologicalComplex₂.ι_totalDesc, ← Category.assoc, hi, Sigma.ι_desc]

end SerrePositivity.AlgebraicGeometry
