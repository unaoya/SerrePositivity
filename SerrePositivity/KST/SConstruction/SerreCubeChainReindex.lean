module
public import SerrePositivity.KST.SConstruction.SerreCubeChainFace

/-! # 元の鎖立方体の射の始域・終域移送
概要：元の鎖射の両次元を移し、恒等・合成・標準面・実鎖射の比較との整合性を示す。
方針：次元等号を消去して、元の同じ鎖射の法則へ戻す。
規約：元の鎖複体と射を保持。使われ方：右側自由座標付き標準面の読み替え次元。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A]

/-- 元の鎖立方体の実射の始域と終域を、同じ次元等号で移す。 -/
def serreCubeChainReindex {p q p' q' : ℕ} (hp : p' = p) (hq : q = q')
    (f : serreCubeComplex A p ⟶ serreCubeComplex A q) :
    serreCubeComplex A p' ⟶ serreCubeComplex A q' :=
  eqToHom (congrArg (serreCubeComplex A) hp) ≫ f ≫
    eqToHom (congrArg (serreCubeComplex A) hq)

/-- 元の両次元を移しても、元の同じ実射と異種等号で一致する。 -/
lemma serreCubeChainReindex_heq {p q p' q' : ℕ} (hp : p' = p) (hq : q = q')
    (f : serreCubeComplex A p ⟶ serreCubeComplex A q) :
    HEq (serreCubeChainReindex A hp hq f) f := by
  cases hp
  cases hq
  simp only [serreCubeChainReindex, eqToHom_refl, Category.id_comp, Category.comp_id]
  rfl

/-- 元の恒等射の両次元移送は、元の同じ恒等射。 -/
lemma serreCubeChainReindex_id {p p' : ℕ} (hp : p' = p) :
    serreCubeChainReindex A hp hp.symm (𝟙 (serreCubeComplex A p)) =
      𝟙 (serreCubeComplex A p') := by
  cases hp
  exact Category.id_comp _

/-- 元の中間次元を揃えた両次元移送は、元の射の合成を厳密に保つ。 -/
lemma serreCubeChainReindex_comp {p q r p' q' r' : ℕ}
    (hp : p' = p) (hq : q' = q) (hr : r' = r)
    (f : serreCubeComplex A p ⟶ serreCubeComplex A q)
    (g : serreCubeComplex A q ⟶ serreCubeComplex A r) :
    serreCubeChainReindex A hp hr.symm (f ≫ g) =
      serreCubeChainReindex A hp hq.symm f ≫ serreCubeChainReindex A hq hr.symm g := by
  cases hp
  cases hq
  cases hr
  simp only [serreCubeChainReindex, eqToHom_refl, Category.id_comp, Category.comp_id]

/-- 元の標準面の両次元移送は、元の同じ数値座標の標準面。 -/
lemma serreCubeChainReindex_face (b : Bool) {p q p' q' : ℕ}
    (hp : p' = p) (hq : q' = q) (h : p + 1 = q) (h' : p' + 1 = q') (i : Fin q) :
    serreCubeChainReindex A hp hq.symm (serreCubeChainFace A b p q h i) =
      serreCubeChainFace A b p' q' h' (Fin.cast hq.symm i) := by
  cases hp
  cases hq
  simp only [serreCubeChainReindex, eqToHom_refl, Category.id_comp, Category.comp_id]
  rfl

/-- 元の始域・中間次元と終域複体の等号を保つ鎖射の比較は、実合成へ伝播する。 -/
lemma serreCubeChain_comp_heq {p q p' q' : ℕ} (hp : p = p') (hq : q = q')
    {K K' : Complex A} (hK : K = K')
    (f : serreCubeComplex A p ⟶ serreCubeComplex A q)
    (f' : serreCubeComplex A p' ⟶ serreCubeComplex A q')
    (g : serreCubeComplex A q ⟶ K) (g' : serreCubeComplex A q' ⟶ K')
    (hf : HEq f f') (hg : HEq g g') : HEq (f ≫ g) (f' ≫ g') := by
  cases hp
  cases hq
  cases hK
  cases eq_of_heq hf
  cases eq_of_heq hg
  rfl

end SerrePositivity.KST.SConstruction
