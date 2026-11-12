module
public import SerrePositivity.KST.SConstruction.SimplexIntervalComposeStandardCube
public import SerrePositivity.KST.SConstruction.SerreCubeRightExtensionFace

/-! # 元の標準区間合成 cube の実 Serre 右面
概要：元の二区間合成 cube を同じ標準区間次元で鎖化し、元の右面を回収する。
方針：標準 cube 一面公式へ元の鎖関手を適用し、次元移送の合成を照合する。
規約：元の右端座標と実鎖射を保持。使われ方：native HA 逆鎖射の厳密合成保存。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A]

/-- 元の標準区間合成 cube の実鎖射は、同じ共有頂点の元の右面と次元移送。 -/
lemma simplexIntervalComposeStandardCube_serre {N : ℕ} (a b c : Fin (N + 1))
    (hab : a < b) (hbc : b < c) :
    (serreConcreteCubeComplexFunctor A).map
        (simplexIntervalComposeStandardCube.{u} a b c hab hbc) =
      (serreCubeRightFace A true (b.val - a.val - 1) (c.val - b.val - 1)).hom ≫
        eqToHom (congrArg (serreCubeComplex A)
          (simplexHAStrictInterval_split_dimension a b c hab hbc).symm) := by
  let n := b.val - a.val - 1
  let m := c.val - b.val - 1
  have hc : c.val - a.val - 1 = (n + m) + 1 := by
    have h := simplexHAStrictInterval_split_dimension a b c hab hbc
    omega
  let e := concreteCubeDimensionIso
    (X := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk (c.val - a.val - 1))
    (Y := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube.mk ((n + m) + 1)) hc
  have hf := (Iso.eq_comp_inv e).mpr
    (simplexIntervalComposeStandardCube_one_face.{u} a b c hab hbc)
  have h := congrArg ((serreConcreteCubeComplexFunctor A).map) hf
  have hd := serreCubeComplexMap_dimension_inv A hc
  have hface : (serreConcreteCubeComplexFunctor A).map
      (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.concreteCubeFace true (n + m) ⟨m, by omega⟩) =
      (serreCubeFace A true (n + m) ⟨m, by omega⟩).hom :=
    congrArg ((Comon.forget (Complex A)).map)
      (serreConcreteCubeFunctor_face A true (n + m) ⟨m, by omega⟩)
  have h₁ : (serreConcreteCubeComplexFunctor A).map
      (simplexIntervalComposeStandardCube.{u} a b c hab hbc) =
      (serreCubeFace A true (n + m) ⟨m, by omega⟩).hom ≫
        eqToHom (congrArg (serreCubeComplex A) hc.symm) :=
    h.trans (((serreConcreteCubeComplexFunctor A).map_comp _ _).trans
      ((congrArg (fun f => f ≫ (serreConcreteCubeComplexFunctor A).map e.inv) hface).trans
        (congrArg (fun f => (serreCubeFace A true (n + m) ⟨m, by omega⟩).hom ≫ f) hd)))
  have hs : (n + m) + 1 = (n + 1) + m := by omega
  have ht := (simplexHAStrictInterval_split_dimension a b c hab hbc).symm
  have h₂ : eqToHom (congrArg (serreCubeComplex A) hc.symm) =
      eqToHom (congrArg (serreCubeComplex A) hs) ≫
        eqToHom (congrArg (serreCubeComplex A) ht) := (eqToHom_trans _ _).symm
  have hr : (serreCubeRightFace A true n m).hom =
      (serreCubeFace A true (n + m) ⟨m, by omega⟩).hom ≫
        eqToHom (congrArg (serreCubeComplex A) hs) := by
    change ((serreCubeFace A true (n + m) ⟨m, by omega⟩) ≫
      serreCubeDimensionMap A hs).hom = _
    rw [Comon.comp_hom', serreCubeDimensionMap_hom]
  exact h₁.trans ((congrArg (fun f =>
    (serreCubeFace A true (n + m) ⟨m, by omega⟩).hom ≫ f) h₂).trans
      ((Category.assoc _ _ _).symm.trans
        (congrArg (fun f => f ≫ eqToHom (congrArg (serreCubeComplex A) ht)) hr.symm)))

end SerrePositivity.KST.SConstruction
