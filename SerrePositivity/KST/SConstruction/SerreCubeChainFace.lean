module
public import SerrePositivity.KST.SConstruction.SerreCubeDimensionTransport
public import SerrePositivity.KST.SConstruction.SerreCubeFaceRelations

/-! # 元の Serre 鎖面の始域・終域の次元指定
概要：元の零面・一面を、指定した余次元一の始域と終域の間の実鎖射として読む。
方針：元の面射と元の次元等号による移送だけを使う。
規約：元の面と数値座標を保持。使われ方：読み替え次元での実部分集合生成射の比較。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A]

/-- 元の逆次元構造射の鎖は、同じ等号に沿う元の鎖複体の移送。 -/
lemma serreCubeComplexMap_dimension_inv {p q : ℕ} (h : p = q) :
    (serreConcreteCubeComplexFunctor A).map
        (concreteCubeDimensionIso (X := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk p) (Y := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk q) h).inv =
      eqToHom (congrArg (serreCubeComplex A) h.symm) := by
  cases h
  change (serreConcreteCubeComplexFunctor A).map (𝟙 (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk p)) = 𝟙 _
  exact (serreConcreteCubeComplexFunctor A).map_id _

/-- 元の鎖面を、余次元一の同じ指定始域・終域の間で読む。 -/
def serreCubeChainFace (b : Bool) (p q : ℕ) (h : p + 1 = q) (i : Fin q) :
    serreCubeComplex A p ⟶ serreCubeComplex A q :=
  (serreCubeFace A b p (Fin.cast h.symm i)).hom ≫
    eqToHom (congrArg (serreCubeComplex A) h)

/-- 終域が元の一段上の次元なら、元の同じ鎖面を回収する。 -/
lemma serreCubeChainFace_refl (b : Bool) (p : ℕ) (i : Fin (p + 1)) :
    serreCubeChainFace A b p (p + 1) rfl i = (serreCubeFace A b p i).hom := by
  exact Category.comp_id _

/-- 元の始域・終域の次元移送は、同じ数値座標の元の鎖面と厳密に可換。 -/
lemma serreCubeChainFace_naturality (b : Bool) {p q p' q' : ℕ}
    (hp : p' = p) (hq : q' = q) (h : p + 1 = q) (h' : p' + 1 = q') (i : Fin q) :
    serreCubeChainFace A b p' q' h' (Fin.cast hq.symm i) ≫
        eqToHom (congrArg (serreCubeComplex A) hq) =
      eqToHom (congrArg (serreCubeComplex A) hp) ≫ serreCubeChainFace A b p q h i := by
  cases hp
  cases hq
  simp only [eqToHom_refl, Category.comp_id, Category.id_comp, Fin.cast_refl]
  rfl

end SerrePositivity.KST.SConstruction
