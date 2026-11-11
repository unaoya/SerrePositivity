module

public import SerrePositivity.KST.Spectra.SphereSimplex
public import SerrePositivity.KST.Spectra.UnbasedHomotopyIsomorphism

/-!
概要：球面上の非基点固定ホモトピーを、正次数の群の実際の基点 path へ移す。
方針：ホモトピーの指数転置を点つき球面射とし、その一つの類を両端で評価する。
規約：単体上の非相対ホモトピーから群の等式を推論しない。
使われ方：全空間への有限球面の fiber 検出から全基点 π の代表元検出へ進む。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.PiCriterion
open KST.Spectra

/-- 指定頂点を基点にしても基礎 Kan 複体は同じ。 -/
instance ofVertex_right_kanComplex (X : SSet.{u}) [KanComplex X] (x : X _⦋0⦌) :
    KanComplex (PointedSimplicialSet.ofVertex X x).right :=
  inferInstanceAs (KanComplex X)

/-- 点つき球面射が表す正次数の類。 -/
def sphereClass {X : PointedSimplicialSet.{u}} [KanComplex X.right] (n : ℕ)
    (f : PointedSimplicialSet.sphere.{u} (n + 1) ⟶ X) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup X.right n X.basepoint :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk (SphereSimplex.equiv X (n + 1) f)

/-- 任意の正次数の類は実際の有限球面の点つき射で表せる。 -/
lemma sphereClass_surjective (X : PointedSimplicialSet.{u}) [KanComplex X.right] (n : ℕ) :
    Function.Surjective (sphereClass (X := X) n) := by
  intro a
  obtain ⟨s, rfl⟩ := Quotient.mk_surjective a
  refine ⟨(SphereSimplex.equiv X (n + 1)).symm s, ?_⟩
  simp only [sphereClass, Equiv.apply_symm_apply, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk]

/-- 元の射を保持し、その基点の像を標的の基点に指定する。 -/
def pointedImageMap {A : PointedSimplicialSet.{u}} {Y : SSet.{u}} (f : A.right ⟶ Y) :
    A ⟶ PointedSimplicialSet.ofVertex Y (f.app _ A.basepoint) :=
  Under.homMk f (by
    apply (SSet.unitHomEquiv Y).injective
    change f.app _ A.basepoint =
      (SSet.unitHomEquiv Y) ((SSet.unitHomEquiv Y).symm (f.app _ A.basepoint))
    exact ((SSet.unitHomEquiv Y).apply_symm_apply _).symm)

/-- 球面の代表の類は、指定した点つき射の後合成と可換。 -/
lemma sphereClass_post {X Y : PointedSimplicialSet.{u}}
    [KanComplex X.right] [KanComplex Y.right] (n : ℕ)
    (f : PointedSimplicialSet.sphere.{u} (n + 1) ⟶ X) (p : X ⟶ Y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map p.right (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint p) (sphereClass n f) =
      sphereClass n (f ≫ p) := by
  dsimp only [sphereClass]
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map_mk, SphereSimplex.equiv_comp]

/-- 球面上の実際のホモトピーは、両端の群の類を同じ path 対象の類から得る。 -/
lemma sphereClass_path_witness {X : SSet.{u}} [KanComplex X]
    (n : ℕ) (x y : X _⦋0⦌)
    (f : PointedSimplicialSet.sphere.{u} (n + 1) ⟶ PointedSimplicialSet.ofVertex X x)
    (g : PointedSimplicialSet.sphere.{u} (n + 1) ⟶ PointedSimplicialSet.ofVertex X y)
    (H : SSet.Homotopy f.right g.right) :
    ∃ z : (KanPath.object X) _⦋0⦌,
      ∃ h₀ : (KanPath.evaluation X 0).app _ z =
        (PointedSimplicialSet.ofVertex X x).basepoint,
      ∃ h₁ : (KanPath.evaluation X 1).app _ z =
        (PointedSimplicialSet.ofVertex X y).basepoint,
      ∃ a : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (KanPath.object X) n z,
        _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map (KanPath.evaluation X 0) h₀ a = sphereClass n f ∧
        _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map (KanPath.evaluation X 1) h₁ a = sphereClass n g := by
  let S := PointedSimplicialSet.sphere.{u} (n + 1)
  let P : PointedSimplicialSet.{u} := Under.mk (S.hom ≫ KanPath.transpose H)
  have : KanComplex P.right := inferInstanceAs (KanComplex (KanPath.object X))
  let t : S ⟶ P := Under.homMk (KanPath.transpose H) rfl
  let e₀ : P ⟶ PointedSimplicialSet.ofVertex X x :=
    Under.homMk (KanPath.evaluation X 0) (by
      change (S.hom ≫ KanPath.transpose H) ≫ KanPath.evaluation X 0 = _
      rw [Category.assoc, KanPath.transpose_zero]
      exact Under.w f)
  let e₁ : P ⟶ PointedSimplicialSet.ofVertex X y :=
    Under.homMk (KanPath.evaluation X 1) (by
      change (S.hom ≫ KanPath.transpose H) ≫ KanPath.evaluation X 1 = _
      rw [Category.assoc, KanPath.transpose_one]
      exact Under.w g)
  have h₀ : (KanPath.evaluation X 0).app _ P.basepoint =
      (PointedSimplicialSet.ofVertex X x).basepoint :=
    _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint e₀
  have h₁ : (KanPath.evaluation X 1).app _ P.basepoint =
      (PointedSimplicialSet.ofVertex X y).basepoint :=
    _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint e₁
  have ht₀ : t ≫ e₀ = f := Under.UnderMorphism.ext (KanPath.transpose_zero H)
  have ht₁ : t ≫ e₁ = g := Under.UnderMorphism.ext (KanPath.transpose_one H)
  refine ⟨P.basepoint, h₀, h₁, sphereClass n t, ?_, ?_⟩
  · have h := sphereClass_post n t e₀
    rw [ht₀] at h
    dsimp only [e₀, PointedSimplicialSet.ofVertex] at h
    exact h
  · have h := sphereClass_post n t e₁
    rw [ht₁] at h
    dsimp only [e₁, PointedSimplicialSet.ofVertex] at h
    exact h

end SerrePositivity.InfinityCategories.Project.DerivedCategories.PiCriterion
