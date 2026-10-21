module
public import SerrePositivity.KST.SConstruction.ConcreteCubeFaceCriterion

/-! # 元の両標準面の次元移送
概要：元の次元等号による構造射の合成と、元の標準面の共役を回収する。
方針：元の自然数の等号を消去する。
規約：零面・一面の元の座標を保持。使われ方：元の分割標準一面の濃度次元表示。
-/
@[expose] public section
namespace SerrePositivity.KST.SConstruction
open CategoryTheory

/-- 元の次元移送の合成は、元の等号の推移による同じ次元移送。 -/
lemma concreteCubeDimensionIso_hom_trans {a b c : ℕ} (h : a = b) (k : b = c) :
    (concreteCubeDimensionIso (X := ConcreteCube.mk a) (Y := ConcreteCube.mk b) h).hom ≫
      (concreteCubeDimensionIso (X := ConcreteCube.mk b) (Y := ConcreteCube.mk c) k).hom =
    (concreteCubeDimensionIso (X := ConcreteCube.mk a) (Y := ConcreteCube.mk c)
      (h.trans k)).hom := by
  cases h
  cases k
  rfl

/-- 元の共通次元を経由する移送は、元の直接の次元等号移送を回収する。 -/
lemma concreteCubeDimensionIso_inv_comp_hom {a b c : ℕ}
    (h : b = a) (k : b = c) (l : a = c) :
    (concreteCubeDimensionIso (X := ConcreteCube.mk b) (Y := ConcreteCube.mk a) h).inv ≫
      (concreteCubeDimensionIso (X := ConcreteCube.mk b) (Y := ConcreteCube.mk c) k).hom =
    (concreteCubeDimensionIso (X := ConcreteCube.mk a) (Y := ConcreteCube.mk c) l).hom := by
  cases h
  cases k
  rfl

/-- 元の標準面の同定は、始域・終域の元の次元移送による共役で保たれる。 -/
lemma concreteCube_face_conjugate (b : Bool) {m n m' n' : ℕ} (hm : m' = m) (hn : n' = n)
    (hc : n = m + 1) (hc' : n' = m' + 1)
    (f : ConcreteCube.mk m ⟶ ConcreteCube.mk n) (i : Fin n)
    (hf : f ≫ (concreteCubeDimensionIso
      (X := ConcreteCube.mk n) (Y := ConcreteCube.mk (m + 1)) hc).hom =
        concreteCubeFace b m (Fin.cast hc i)) :
    ((concreteCubeDimensionIso (X := ConcreteCube.mk m') (Y := ConcreteCube.mk m) hm).hom ≫
        f ≫ (concreteCubeDimensionIso
          (X := ConcreteCube.mk n') (Y := ConcreteCube.mk n) hn).inv) ≫
      (concreteCubeDimensionIso
        (X := ConcreteCube.mk n') (Y := ConcreteCube.mk (m' + 1)) hc').hom =
    concreteCubeFace b m' (Fin.cast hc' (Fin.cast hn.symm i)) := by
  subst m'
  subst n'
  simpa only [concreteCubeDimensionIso, eqToIso_refl, Iso.refl_hom, Iso.refl_inv,
    Category.id_comp, Category.comp_id, Fin.cast_refl, id_eq] using hf

end SerrePositivity.KST.SConstruction
