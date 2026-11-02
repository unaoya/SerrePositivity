module
public import SerrePositivity.DifferentialGraded.Endomorphism.Basic
public import SerrePositivity.DifferentialGraded.Category.Basic

/-! # 元の閉同型による全 dg End の共役
概要：指定閉同型を使い、元の全次数 End 複体の間の dg 関手を構成する。
方針：元の前後合成と enriched composition の自然性・中間同型の消去を使う。
規約：商や局所化の普遍性は扱わない。使われ方：右 cone の元の同型を通す End 比較。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory
open SerrePositivity.DifferentialGraded
variable (R : Type u) [CommRing R] {D : Type v} [DGCategory R D]
  {x y : ClosedCategory R D} (e : x ≅ y)

private lemma homEquiv_pre {a b c : ClosedCategory R D} (f : a ⟶ b) (g : b ⟶ c) :
    eHomEquiv (Complex R) g ≫ eHomWhiskerRight (Complex R) f c =
      eHomEquiv (Complex R) (f ≫ g) := by
  rw [eHomEquiv_comp, eHomWhiskerRight, ← Category.assoc, leftUnitor_inv_naturality]
  simp only [tensorHom_def', Category.assoc]

private lemma homEquiv_post {a b c : ClosedCategory R D} (f : a ⟶ b) (g : b ⟶ c) :
    eHomEquiv (Complex R) f ≫ eHomWhiskerLeft (Complex R) a g =
      eHomEquiv (Complex R) (f ≫ g) := by
  rw [eHomEquiv_comp, eHomWhiskerLeft, ← Category.assoc, rightUnitor_inv_naturality]
  simp only [Category.assoc, tensorHom_def, unitors_inv_equal]

/-- 同じ閉同型の逆射で前合成し、元の順射で後合成する実 End 鎖写像。 -/
def dgEndIsoHom :
    (x ⟶[Complex R] x) ⟶ (y ⟶[Complex R] y) :=
  eHomWhiskerRight (Complex R) e.inv x ≫ eHomWhiskerLeft (Complex R) y e.hom

/-- 同じ実 End 鎖写像は元の単位を保つ。 -/
lemma dgEndIsoHom_unit :
    eId (Complex R) x ≫ dgEndIsoHom R e = eId (Complex R) y := by
  rw [dgEndIsoHom, ← eHomEquiv_id (Complex R) x, ← Category.assoc,
    homEquiv_pre, Category.comp_id, homEquiv_post, e.inv_hom_id, eHomEquiv_id]

/-- 同じ実 End 鎖写像は全 Hom の元の豊穣合成を保つ。 -/
lemma dgEndIsoHom_comp :
    eComp (Complex R) x x x ≫ dgEndIsoHom R e =
      (dgEndIsoHom R e ⊗ₘ dgEndIsoHom R e) ≫ eComp (Complex R) y y y := by
  have hL : eComp (Complex R) x x x ≫ dgEndIsoHom R e =
      (eHomWhiskerRight (Complex R) e.inv x ⊗ₘ eHomWhiskerLeft (Complex R) x e.hom) ≫
        eComp (Complex R) y x y := by
    rw [dgEndIsoHom, ← Category.assoc, eComp_eHomWhiskerRight,
      Category.assoc, eComp_eHomWhiskerLeft, ← Category.assoc, ← tensorHom_def]
  have hR : (dgEndIsoHom R e ⊗ₘ dgEndIsoHom R e) ≫ eComp (Complex R) y y y =
      (eHomWhiskerRight (Complex R) e.inv x ⊗ₘ eHomWhiskerLeft (Complex R) x e.hom) ≫
        eComp (Complex R) y x y := by
    calc
      _ = ((eHomWhiskerRight (Complex R) e.inv x ≫
              eHomWhiskerLeft (Complex R) y e.hom) ⊗ₘ
            (eHomWhiskerLeft (Complex R) x e.hom ≫
              eHomWhiskerRight (Complex R) e.inv y)) ≫ eComp (Complex R) y y y := by
        exact congrArg (fun z => (dgEndIsoHom R e ⊗ₘ z) ≫ eComp (Complex R) y y y)
          (eHom_whisker_exchange (Complex R) e.inv e.hom).symm
      _ = _ := by
        have hc : (eHomWhiskerLeft (Complex R) y e.hom ⊗ₘ
            eHomWhiskerRight (Complex R) e.inv y) ≫ eComp (Complex R) y y y =
            eComp (Complex R) y x y := by
          rw [tensorHom_def, Category.assoc, eHom_whisker_cancel]
        rw [← tensorHom_comp_tensorHom, Category.assoc, hc]
  exact hL.trans hR.symm

/-- 同じ元の閉同型を使う、一対象の全 dg End の間の共役関手。 -/
def dgEndIsoFunctor :
    DGFunctor R (EndomorphismObject (ForgetEnrichment.to (Complex R) x))
      (EndomorphismObject (ForgetEnrichment.to (Complex R) y)) where
  obj _ := .point
  map _ _ := dgEndIsoHom R e
  map_id _ := dgEndIsoHom_unit R e
  map_comp _ _ _ := dgEndIsoHom_comp R e

/-- 同じ End 関手の全 Hom 作用は元の前後合成そのもの。 -/
lemma dgEndIsoFunctor_map (a b : EndomorphismObject (ForgetEnrichment.to (Complex R) x)) :
    (dgEndIsoFunctor R e).map a b = dgEndIsoHom R e := rfl

end SerrePositivity.KST.SConstruction
