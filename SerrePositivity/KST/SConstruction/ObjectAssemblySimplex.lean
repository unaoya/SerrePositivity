module
public import SerrePositivity.KST.SConstruction.ObjectSConstruction
public import SerrePositivity.KST.SConstruction.DiagonalAssembly

/-! # object の単体と元の対角組み立ての照合
概要：object/core 比較で得た単体を、同じ頂点をパラメータとする組み立てで表示する。
方針：内部の定数退化に関する自然性を各単体で使う。
規約：任意の二重単体集合に適用する。使われ方：S₁ の対象 loop と S₂ の辺の照合。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial

/-- object の単体の対角への像は、その内部頂点での元の組み立てに等しい。 -/
lemma diagonalObjectInclusion_simplex (X : SimplexCategoryᵒᵖ ⥤ SSet.{u}) (n : ℕ)
    (e : (diagonalObjects X) _⦋n⦌) :
    SSet.yonedaEquiv.symm e ≫ diagonalObjectInclusion X =
      lift (𝟙 (Δ[n] : SSet.{u})) (SSet.const e) ≫ diagonalAssembly n X := by
  apply NatTrans.ext
  funext d
  apply ConcreteCategory.hom_ext
  intro a
  have hn := ConcreteCategory.congr_hom
    ((X.map (stdSimplex.objEquiv a).op).naturality
      (SimplexCategory.const d.unop ⦋0⦌ 0).op) e
  exact hn.symm

/-- 元の gapped object の単体は同じ core 頂点での元の組み立てに等しい。 -/
lemma objectToCoreSRealization_simplex (C : SSet.{u}) (n : ℕ)
    (e : (objectSConstruction C) _⦋n⦌) :
    SSet.yonedaEquiv.symm e ≫ objectToCoreSRealization C =
      lift (𝟙 (Δ[n] : SSet.{u}))
        (SSet.const (⟨e, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore_vertex
          (X := sConstruction n C) e⟩ : (coreSConstruction n C) _⦋0⦌)) ≫
        diagonalAssembly n (simplicialCoreSConstruction C) := by
  have h := congrArg (fun g => g ≫ diagonalObjectInclusion (simplicialCoreSConstruction C))
    (SSet.yonedaEquiv_symm_comp e (objectSCoreVertexIso C).hom)
  exact (Category.assoc _ _ _).symm.trans
    (h.trans (diagonalObjectInclusion_simplex (simplicialCoreSConstruction C) n _))

end SerrePositivity.KST.SConstruction
