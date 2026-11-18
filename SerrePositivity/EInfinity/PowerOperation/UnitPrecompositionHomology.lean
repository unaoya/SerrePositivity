module

public import SerrePositivity.HomologicalAlgebra.Complexes.HomologyZero.HomotopyClasses
public import SerrePositivity.EInfinity.BarrattEccles.Theory.HomologyAlgebraFunctor

/-!
# 単位複体の自己同型による H⁰ の全単射と自然変換の検出

DAG XIII §2.2 の零次数の Ω 比較への前段。単位からの鎖ホモトピー類の
既存の H⁰ 表示と、元の単位の自己同型への前合成を使う。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.PowerOperation
open CategoryTheory HomologicalComplex MonoidalCategory
open SerrePositivity.DifferentialGraded _root_.SerrePositivity.HomologyZero
variable {A : Type u} [CommRing A]

/-- 実単位自己同型の前合成を同じ鎖ホモトピー圏で行う同値。 -/
def unitPrecompositionEquiv (e : 𝟙_ (Complex A) ≅ 𝟙_ (Complex A)) (M : Complex A) :
    ((HomotopyCategory.quotient (ModuleCat A) (.up ℤ)).obj (𝟙_ (Complex A)) ⟶
      (HomotopyCategory.quotient (ModuleCat A) (.up ℤ)).obj M) ≃
    ((HomotopyCategory.quotient (ModuleCat A) (.up ℤ)).obj (𝟙_ (Complex A)) ⟶
      (HomotopyCategory.quotient (ModuleCat A) (.up ℤ)).obj M) where
  toFun f := (HomotopyCategory.quotient (ModuleCat A) (.up ℤ)).map e.hom ≫ f
  invFun f := (HomotopyCategory.quotient (ModuleCat A) (.up ℤ)).map e.inv ≫ f
  left_inv f := by
    dsimp only
    rw [← Category.assoc, ← CategoryTheory.Functor.map_comp, e.inv_hom_id,
    CategoryTheory.Functor.map_id, Category.id_comp]
  right_inv f := by
    dsimp only
    rw [← Category.assoc, ← CategoryTheory.Functor.map_comp, e.hom_inv_id,
    CategoryTheory.Functor.map_id, Category.id_comp]

/-- 元の単位自己同型の作用を H⁰ の集合の同値へ運ぶ。 -/
def unitPrecompositionHomologyEquiv (e : 𝟙_ (Complex A) ≅ 𝟙_ (Complex A)) (M : Complex A) :
    M.homology 0 ≃ M.homology 0 :=
  (_root_.SerrePositivity.HomologyZero.unitHomLinearEquiv M).toEquiv.symm.trans
    ((unitPrecompositionEquiv e M).trans (_root_.SerrePositivity.HomologyZero.unitHomLinearEquiv M).toEquiv)

lemma unitPrecompositionHomologyEquiv_class (e : 𝟙_ (Complex A) ≅ 𝟙_ (Complex A))
    (M : Complex A) (f : 𝟙_ (Complex A) ⟶ M) :
    unitPrecompositionHomologyEquiv e M (_root_.SerrePositivity.HomologyZero.unitClass M f) = _root_.SerrePositivity.HomologyZero.unitClass M (e.hom ≫ f) := by
  have hf : (_root_.SerrePositivity.HomologyZero.unitHomLinearEquiv M).symm (_root_.SerrePositivity.HomologyZero.unitClass M f) =
      (HomotopyCategory.quotient (ModuleCat A) (.up ℤ)).map f := by
    apply (_root_.SerrePositivity.HomologyZero.unitHomLinearEquiv M).injective
    rw [LinearEquiv.apply_symm_apply]
    exact (_root_.SerrePositivity.HomologyZero.homotopyClassMap_apply_map M f).symm
  change _root_.SerrePositivity.HomologyZero.unitHomLinearEquiv M
    ((HomotopyCategory.quotient (ModuleCat A) (.up ℤ)).map e.hom ≫
      (_root_.SerrePositivity.HomologyZero.unitHomLinearEquiv M).symm (_root_.SerrePositivity.HomologyZero.unitClass M f)) = _
  rw [hf, ← CategoryTheory.Functor.map_comp]
  exact _root_.SerrePositivity.HomologyZero.homotopyClassMap_apply_map M _

/-- H⁰ 上の自然な写像が単位の指定類を単位自己同型の類へ送れば、全対象で全単射。 -/
lemma homologyZeroNatural_bijective_of_unit_iso
    (φ : ∀ M : Complex A, M.homology 0 → M.homology 0)
    (hn : ∀ {M N : Complex A} (f : M ⟶ N) (x : M.homology 0),
      φ N ((homologyMap f 0).hom x) = (homologyMap f 0).hom (φ M x))
    (e : 𝟙_ (Complex A) ≅ 𝟙_ (Complex A))
    (hu : φ (𝟙_ (Complex A)) (_root_.SerrePositivity.HomologyZero.unitClass (𝟙_ (Complex A)) (𝟙 _)) =
      _root_.SerrePositivity.HomologyZero.unitClass (𝟙_ (Complex A)) e.hom) (M : Complex A) :
    Function.Bijective (φ M) := by
  have h : φ M = unitPrecompositionHomologyEquiv e M := by
    funext x
    obtain ⟨f, rfl⟩ := _root_.SerrePositivity.HomologyZero.unitClass_surjective M x
    have hh := hn f (_root_.SerrePositivity.HomologyZero.unitClass (𝟙_ (Complex A)) (𝟙 _))
    rw [_root_.SerrePositivity.EInfinity.HomologyZero.unitClass_naturality, Category.id_comp, hu, _root_.SerrePositivity.EInfinity.HomologyZero.unitClass_naturality] at hh
    exact hh.trans (unitPrecompositionHomologyEquiv_class e M f).symm
  rw [h]
  exact (unitPrecompositionHomologyEquiv e M).bijective

end SerrePositivity.EInfinity.PowerOperation
