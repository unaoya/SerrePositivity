module

public import SerrePositivity.AlgebraicGeometry.CechTripleTotalComponents
import all SerrePositivity.HomologicalAlgebra.BicomplexProjection

/-!
概要：複体値の二重複体の三重totalについて、括り方の比較を複体の同型にする。
方針：三方向の標準入射で微分の符号と写像の自然性を照合する。
規約：同じMathlibのtotalと同じ整数係数のままで、仮定を追加しない。
使われ方：複体値の二重Čechの軸比較（承認済み計画C03〜C05）。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory CategoryTheory.Limits Preadditive
universe u
local notation "up" => ComplexShape.up ℕ
set_option backward.isDefEq.respectTransparency false

/-- 三重totalの標準的な成分比較は、元の三方向の微分と可換である。 -/
theorem cechTripleTotalComponentIso_d
    (K : HomologicalComplex₂ (CochainComplex (ModuleCat.{u} ℤ) ℕ) up up) (n : ℕ) :
    (cechTripleTotalComponentIso K n).hom ≫
      (HomologicalComplex₂.total (C := ModuleCat.{u} ℤ)
        ((cechIntegerLiftTotalFunctor.mapHomologicalComplex up).obj K) up).d n (n+1) =
    (HomologicalComplex₂.total (C := ModuleCat.{u} ℤ)
      (HomologicalComplex₂.total (C := CochainComplex (ModuleCat.{u} ℤ) ℕ) K up) up).d n (n+1) ≫
        (cechTripleTotalComponentIso K (n+1)).hom := by
  let KT : HomologicalComplex₂ (ModuleCat.{u} ℤ) up up :=
    HomologicalComplex₂.total (C := CochainComplex (ModuleCat.{u} ℤ) ℕ) K up
  let KM : HomologicalComplex₂ (ModuleCat.{u} ℤ) up up :=
    (cechIntegerLiftTotalFunctor.mapHomologicalComplex up).obj K
  apply HomologicalComplex₂.total.hom_ext (K := KT)
  intro d c hdc
  apply (isColimitOfHasCoproductOfPreservesColimit
    (HomologicalComplex.eval (ModuleCat.{u} ℤ) up c)
    (K.toGradedObject.mapObjFun (ComplexShape.π up up up) d)).hom_ext
  rintro ⟨⟨⟨a,b⟩,hab⟩⟩
  have hab' : a+b=d := hab
  subst d
  have hn : a+b+c=n := hdc
  have hleft := congrArg (fun f ↦ f.f c)
    (SerrePositivity.HomologicalAlgebra.total_d_summand K a b (a+b) rfl)
  simp only [HomologicalComplex.comp_f, HomologicalComplex.add_f_apply,
    HomologicalComplex.zsmul_f_apply] at hleft
  have hright := SerrePositivity.HomologicalAlgebra.total_d_summand (K.X a) b c (b+c) rfl
  have houterL := SerrePositivity.HomologicalAlgebra.total_d_summand KT (a+b) c n hn
  have houterR := SerrePositivity.HomologicalAlgebra.total_d_summand KM a (b+c) n
    (by change a+(b+c)=n; omega)
  have hmap := HomologicalComplex₂.ιTotal_map (K := K.X a) (L := K.X (a+1)) (φ := K.d a (a+1)) (c₁₂ := up) b c (b+c) rfl
  change HomologicalComplex₂.ιTotal (K.X a) up b c (b+c) rfl ≫
    (KM.d a (a+1)).f (b+c) = _ at hmap
  change HomologicalComplex₂.ιTotal (K.X a) up b c (b+c) rfl ≫
    (KM.X a).d (b+c) (b+c+1) = _ at hright
  change (HomologicalComplex₂.ιTotal K up a b (a+b) rfl).f c ≫
    (KT.d (a+b) (a+b+1)).f c = _ at hleft
  have hcomm := (HomologicalComplex₂.ιTotal K up a b (a+b) rfl).comm c (c+1)
  change (HomologicalComplex₂.ιTotal K up a b (a+b) rfl).f c ≫
    (KT.X (a+b)).d c (c+1) = _ at hcomm
  change (HomologicalComplex₂.ιTotal K up a b (a+b) rfl).f c ≫
    KT.ιTotal up (a+b) c n hn ≫ (cechTripleTotalComponentIso K n).hom ≫
      (HomologicalComplex₂.total KM up).d n (n+1) =
    (HomologicalComplex₂.ιTotal K up a b (a+b) rfl).f c ≫
      KT.ιTotal up (a+b) c n hn ≫ (HomologicalComplex₂.total KT up).d n (n+1) ≫
        (cechTripleTotalComponentIso K (n+1)).hom
  rw [← Category.assoc, ← Category.assoc,
    cechTripleTotalComponentIso_ι K a b c n hn]
  rw [Category.assoc, houterR]
  rw [comp_add, comp_zsmul, ← Category.assoc, hmap]
  rw [← Category.assoc, hright, add_comp, zsmul_comp]
  simp only [Category.assoc]
  rw [reassoc_of% houterL]
  simp only [comp_add, comp_zsmul, add_comp, zsmul_comp, Category.assoc]
  rw [reassoc_of% hleft, reassoc_of% hcomm]
  have hi (x y z d e m : ℕ) (hd : x+y=d) (he : y+z=e) (hm : d+z=m) :
      (HomologicalComplex₂.ιTotal K up x y d hd).f z ≫
        KT.ιTotal up d z m hm ≫ (cechTripleTotalComponentIso K m).hom =
      HomologicalComplex₂.ιTotal (K.X x) up y z e he ≫
        KM.ιTotal up x e m (by change x+e=m; omega) := by
    subst d e
    exact (Category.assoc _ _ _).symm.trans
      (cechTripleTotalComponentIso_ι K x y z m hm)
  simp only [add_comp, zsmul_comp, Category.assoc]
  rw [hi (a+1) b c (a+b+1) (b+c) (n+1) (by omega) rfl (by omega),
    hi a (b+1) c (a+b+1) (b+c+1) (n+1) (by omega) (by omega) (by omega),
    hi a b (c+1) (a+b) (b+c+1) (n+1) rfl (by omega) (by omega)]
  simp only [smul_add, smul_smul, ← pow_add, add_assoc]

/-- 元の三重totalの二つの括り方の標準的な余鎖複体の同型。 -/
def cechTripleTotalAssociator
    (K : HomologicalComplex₂ (CochainComplex (ModuleCat.{u} ℤ) ℕ) up up) :
    HomologicalComplex₂.total (C := ModuleCat.{u} ℤ)
      (HomologicalComplex₂.total (C := CochainComplex (ModuleCat.{u} ℤ) ℕ) K up) up ≅
    HomologicalComplex₂.total (C := ModuleCat.{u} ℤ)
      ((cechIntegerLiftTotalFunctor.mapHomologicalComplex up).obj K) up :=
  HomologicalComplex.Hom.isoOfComponents (cechTripleTotalComponentIso K) (by
    intro i j hij
    have h : i+1=j := hij
    subst j
    exact cechTripleTotalComponentIso_d K i)

/-- 三重totalの標準同型は元の複体値の二重複体の射に自然である。 -/
theorem cechTripleTotalAssociator_naturality
    {K L : HomologicalComplex₂ (CochainComplex (ModuleCat.{u} ℤ) ℕ) up up} (f : K ⟶ L) :
    HomologicalComplex₂.total.map (HomologicalComplex₂.total.map f up) up ≫
      (cechTripleTotalAssociator L).hom =
    (cechTripleTotalAssociator K).hom ≫ HomologicalComplex₂.total.map
      ((cechIntegerLiftTotalFunctor.mapHomologicalComplex up).map f) up := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply HomologicalComplex₂.total.hom_ext
  intro d c hdc
  apply (isColimitOfHasCoproductOfPreservesColimit
    (HomologicalComplex.eval (ModuleCat.{u} ℤ) up c)
    (K.toGradedObject.mapObjFun (ComplexShape.π up up up) d)).hom_ext
  rintro ⟨⟨⟨a,b⟩,hab⟩⟩
  have hab' : a+b=d := hab
  subst d
  have hn : a+b+c=n := hdc
  have hf := congrArg (fun F ↦ F.f c)
    (HomologicalComplex₂.ιTotal_map (K := K) (L := L) (φ := f)
      (c₁₂ := up) a b (a+b) rfl)
  simp only [HomologicalComplex.comp_f] at hf
  change (HomologicalComplex₂.ιTotal K up a b (a+b) rfl).f c ≫
    HomologicalComplex₂.ιTotal (C := ModuleCat.{u} ℤ) (K.total up) up (a+b) c n hn ≫
      (HomologicalComplex₂.total.map (HomologicalComplex₂.total.map f up) up).f n ≫
        (cechTripleTotalComponentIso L n).hom =
    (HomologicalComplex₂.ιTotal K up a b (a+b) rfl).f c ≫
      HomologicalComplex₂.ιTotal (C := ModuleCat.{u} ℤ) (K.total up) up (a+b) c n hn ≫
        (cechTripleTotalComponentIso K n).hom ≫
          (HomologicalComplex₂.total.map
            ((cechIntegerLiftTotalFunctor.mapHomologicalComplex up).map f) up).f n
  rw [HomologicalComplex₂.ιTotal_map_assoc, ← Category.assoc, hf, Category.assoc,
    ← Category.assoc ((HomologicalComplex₂.ιTotal L up a b (a+b) rfl).f c),
    cechTripleTotalComponentIso_ι L a b c n hn]
  rw [reassoc_of% (cechTripleTotalComponentIso_ι K a b c n hn),
    HomologicalComplex₂.ιTotal_map]
  change _ = HomologicalComplex₂.ιTotal (K.X a) up b c (b+c) rfl ≫
    (HomologicalComplex₂.total.map (f.f a) up).f (b+c) ≫ _
  rw [HomologicalComplex₂.ιTotal_map_assoc]

end SerrePositivity.AlgebraicGeometry
